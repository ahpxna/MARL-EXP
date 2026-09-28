"""Extra comparators on a finished cheap pilot (read-only; loads checkpoints, writes nothing).

critic_chain         : ONE nested priority prepared before the grant from the learned critic
                       (DP over chains maximising sum_k fhat(C_k)); deploy its k-prefix.
critic_chain_R1      : that priority + R=1 repair scored by the same critic.
critic_unrestricted  : argmax of the critic over all k-sets (= per-budget table, 1 forward pass).
learned_score_prefix, learned_repair_R1, direct_budget_network: as in the pilot.
Regret = true best k-set value - true value of the chosen set; mean over (context,k) per
test episode, then over episodes.  Also counts critic evaluations needed AFTER the grant.
"""
import gzip, json, sys
from pathlib import Path
import numpy as np
import torch
ROOT = Path('/Users/phanan/cig-amf-main'); sys.path.insert(0, str(ROOT))
from scripts.MARL_cheap_pilot import SelectorNet, masks_from_logits, load_dataset
from models.marl_revision_selector import reachable_sets
from models.marl_screening import mask_of, layer_masks

def chain_from(fh, m):
    best = {k: max(fh[s] for s in layer_masks(m, k)) for k in range(1, m)}
    dp = {0: (0.0, [])}
    for k in range(1, m):
        nd = {}
        for C0, (v0, path) in dp.items():
            for i in range(m):
                if not (C0 >> i) & 1:
                    C = C0 | (1 << i); val = v0 + best[k] - fh[C]
                    if C not in nd or val < nd[C][0]:
                        nd[C] = (val, path + [i])
        dp = nd
    _, path = min(dp.values(), key=lambda t: t[0])
    rest = [i for i in range(m) if i not in path]
    return tuple(path + rest)

SPLIT = 'test'
def main(run):
    run = Path(run); manifest, rows, splits = load_dataset(run / 'data')
    m = rows[0]['m']
    X = np.asarray([r['features'] for r in rows], dtype=np.float32)
    Y = np.asarray([r['values'] for r in rows], dtype=np.float64)
    masks = torch.tensor([[(s >> i) & 1 for i in range(m)] for s in range(1 << m)], dtype=torch.float32)
    budgets = torch.arange(1, m, dtype=torch.float32)[:, None] / m
    allres = {}
    for ck in sorted((run / 'models').glob('seed_*.pt')):
        blob = torch.load(ck, weights_only=False)
        nets = {}
        for kind, sd in blob['networks'].items():
            net = SelectorNet(blob['input_dim'], m, kind, blob['hidden']); net.load_state_dict(sd); net.eval(); nets[kind] = net
        mean = np.asarray(blob['normalization']['mean']); std = np.asarray(blob['normalization']['std'])
        xt = torch.as_tensor((X - mean) / std, dtype=torch.float32)
        idx = splits[SPLIT]
        with torch.no_grad():
            w = nets['score'](xt[idx]).numpy(); fh = nets['value'](xt[idx], masks).numpy()
            direct = nets['direct'](xt[idx], budgets).numpy()
        per_ep = {}
        for z, i in enumerate(idx):
            f = Y[i]; eid = rows[i]['episode_id']
            rank = tuple(int(a) for a in np.argsort(-w[z], kind='stable'))
            chain = chain_from(fh[z], m)
            for j, k in enumerate(range(1, m)):
                layer = layer_masks(m, k); best = max(f[layer])
                Pc = mask_of(chain[:k]); Ps = mask_of(rank[:k])
                c1 = [mask_of(s) for s in reachable_sets(chain, k, 1)]
                s1 = [mask_of(s) for s in reachable_sets(rank, k, 1)]
                chosen = dict(
                    learned_score_prefix=Ps,
                    learned_repair_R1=max(s1, key=lambda s: fh[z, s]),
                    critic_chain=Pc,
                    critic_chain_R1=max(c1, key=lambda s: fh[z, s]),
                    critic_unrestricted=max(layer, key=lambda s: fh[z, s]),
                    direct_budget_network=int(masks_from_logits(direct[z, j, :], k)),
                    oracle_per_budget=max(layer, key=lambda s: f[s]))
                for meth, s in chosen.items():
                    per_ep.setdefault((meth, eid), []).append(best - f[s])
        methods = sorted({k[0] for k in per_ep})
        res = {}
        for meth in methods:
            eps = [np.mean(v) for (mm, e), v in per_ep.items() if mm == meth]
            res[meth] = dict(mean_episode_regret=float(np.mean(eps)), per_episode=[float(x) for x in eps])
        allres[ck.stem] = res
    methods = list(next(iter(allres.values())).keys())
    print(json.dumps({meth: dict(mean_over_seeds=float(np.mean([allres[s][meth]['mean_episode_regret'] for s in allres])),
                                 by_seed=[round(allres[s][meth]['mean_episode_regret'], 3) for s in allres])
                      for meth in methods}, indent=1))
    evals = {k: dict(R1=1 + k * (m - k), unrestricted=len(layer_masks(m, k))) for k in range(1, m)}
    print('critic evaluations after grant (unrestricted can be tabulated before the grant in one forward pass):', evals)

if __name__ == '__main__':
    SPLIT = sys.argv[2] if len(sys.argv) > 2 else 'test'
    main(sys.argv[1])
