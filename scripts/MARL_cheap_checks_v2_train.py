#!/usr/bin/env python3
"""Cheap checks 1-3 on the v2 tables: information ceiling, fresh bids, unseen budgets.

Offline selector screening on frozen MP2 held-phase values (as MARL_cheap_pilot.py, whose
network class is reused).  Differences from the pilot, all deliberate:
  * feature sets: public (paid past packets + time), bid (+ 1-byte fresh bid per agent,
    charged control), ceiling (+ every agent's CURRENT summary: ORACLE, not deployable);
  * budget regimes: all (train and test on k = 1..m-1) and holdout (train on k in {2,4,6},
    test on k in {3,5,7}; the critic sees only subsets of trained sizes, the direct network
    only trained budgets, and the singleton score is not used because size-1 labels are a
    budget that was held out);
  * the critic loss is centred within each (context, subset size) layer, because only
    within-layer differences decide a k-set; checkpoints of EVERY method are selected by
    validation decision regret at training budgets.
Evaluation reports mean episode regret on held-out TEST episodes and on TRAIN episodes.
"""
from __future__ import annotations
import argparse, copy, gzip, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_cheap_pilot import SelectorNet, masks_from_logits
from models.marl_revision_selector import reachable_sets
from models.marl_screening import mask_of, layer_masks


def load(folder):
    folder = Path(folder)
    man = json.loads((folder / 'manifest.json').read_text())
    if man.get('status') != 'COMPLETE':
        raise ValueError('collection not COMPLETE')
    path = folder / 'tables.jsonl.gz'
    if hashlib.sha256(path.read_bytes()).hexdigest() != man['table_sha256']:
        raise ValueError('table hash mismatch')
    rows = [json.loads(l) for l in gzip.open(path, 'rt')]
    splits, seen = {'train': [], 'val': [], 'test': []}, {}
    for i, r in enumerate(rows):
        if seen.setdefault(r['traffic_seed'], r['split']) != r['split']:
            raise ValueError('traffic seed in two splits')
        splits[r['split']].append(i)
    return man, rows, splits


def features(rows, kind):
    out = []
    for r in rows:
        x = list(r['features'])
        if kind == 'bid':
            x += [b / 255.0 for b in r['bids']]
        elif kind == 'ceiling':
            x += list(r['fresh_features'])
        out.append(x)
    return np.asarray(out, dtype=np.float32)


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
    return tuple(path + [i for i in range(m) if i not in path])


def choose(f, fh, w, direct_logits, heur, m, k, j, use_score):
    layer = layer_masks(m, k)
    chain = chain_from(fh, m)
    c1 = [mask_of(s) for s in reachable_sets(chain, k, 1)]
    out = dict(cached_queue_prefix=mask_of(heur[:k]), critic_chain=mask_of(chain[:k]),
               critic_chain_R1=max(c1, key=lambda s: fh[s]),
               critic_unrestricted=max(layer, key=lambda s: fh[s]),
               direct_budget_network=int(masks_from_logits(direct_logits[j], k)),
               oracle_R1_of_critic_chain=max(c1, key=lambda s: f[s]))
    if use_score:
        rank = tuple(int(a) for a in np.argsort(-w, kind='stable'))
        s1 = [mask_of(s) for s in reachable_sets(rank, k, 1)]
        out.update(learned_score_prefix=mask_of(rank[:k]),
                   learned_repair_R1=max(s1, key=lambda s: fh[s]),
                   oracle_R1_of_score=max(s1, key=lambda s: f[s]))
    return out


def regrets(rows, idx, Y, nets, xt, masks, bud_ev, K_ev, m, use_score):
    with torch.no_grad():
        w = nets['score'](xt[idx]).numpy()
        fh = nets['value'](xt[idx], masks).numpy()
        dl = nets['direct'](xt[idx], bud_ev).numpy()
    per = {}
    for z, i in enumerate(idx):
        f = Y[i]; row = rows[i]
        for j, k in enumerate(K_ev):
            best = max(f[layer_masks(m, k)])
            for meth, s in choose(f, fh[z], w[z], dl[z], row['cached_queue_ranking'], m, k, j,
                                  use_score).items():
                per.setdefault(meth, {}).setdefault(row['episode_id'], []).append(best - f[s])
    return {meth: float(np.mean([np.mean(v) for v in eps.values()])) for meth, eps in per.items()}


def train_one(X, Y, splits, m, K_tr, seed, epochs, hidden, use_score):
    torch.manual_seed(seed); rng = np.random.default_rng(seed)
    tr, va = splits['train'], splits['val']
    mean = X[tr].mean(0); std = X[tr].std(0); std[std < 1e-6] = 1
    xt = torch.as_tensor((X - mean) / std, dtype=torch.float32)
    delta = Y - Y[:, [0]]
    scale = max(float(delta[tr].std()), 1.0)
    yt = torch.as_tensor(delta / scale, dtype=torch.float32)
    masks = torch.tensor([[(s >> i) & 1 for i in range(m)] for s in range(1 << m)], dtype=torch.float32)
    size = masks.sum(1).long()
    bud_tr = torch.tensor(K_tr, dtype=torch.float32)[:, None] / m
    layer_ok = size[None, :] == torch.tensor(K_tr)[:, None]
    lay_idx = {k: torch.nonzero(size == k).flatten() for k in K_tr}
    singleton = torch.tensor([1 << i for i in range(m)])
    nets = {k: SelectorNet(X.shape[1], m, k, hidden) for k in ('score', 'value', 'direct')}
    opts = {k: torch.optim.Adam(n.parameters(), lr=0.003) for k, n in nets.items()}
    best = {k: float('inf') for k in nets}; saved = {}

    def centred(v):
        return torch.cat([v[:, ix] - v[:, ix].mean(1, keepdim=True) for ix in lay_idx.values()], 1)

    for epoch in range(epochs):
        for b in np.array_split(rng.permutation(tr), max(1, (len(tr) + 7) // 8)):
            xb, yb = xt[b], yt[b]
            losses = {}
            if use_score:
                losses['score'] = ((nets['score'](xb) - yb[:, singleton]) ** 2).mean()
            losses['value'] = ((centred(nets['value'](xb, masks)) - centred(yb)) ** 2).mean()
            lg = nets['direct'](xb, bud_tr)
            sl = torch.einsum('bkm,nm->bkn', lg, masks).masked_fill(~layer_ok[None], -torch.inf)
            losses['direct'] = -(sl.softmax(-1) * yb[:, None, :]).sum(-1).mean()
            for k, l in losses.items():
                opts[k].zero_grad(); l.backward(); opts[k].step()
        if epoch % 10 == 0 or epoch == epochs - 1:
            r = regrets_val(X, Y, va, nets, xt, masks, bud_tr, K_tr, m, use_score)
            for k, v in r.items():
                if v < best[k]:
                    best[k] = v; saved[k] = copy.deepcopy(nets[k].state_dict())
    for k, n in nets.items():
        if k in saved:
            n.load_state_dict(saved[k])
        n.eval()
    return nets, xt, masks


def regrets_val(X, Y, va, nets, xt, masks, bud_tr, K_tr, m, use_score):
    with torch.no_grad():
        w = nets['score'](xt[va]).numpy(); fh = nets['value'](xt[va], masks).numpy()
        dl = nets['direct'](xt[va], bud_tr).numpy()
    out = {'score': [], 'value': [], 'direct': []}
    for z, i in enumerate(va):
        f = Y[i]
        rank = np.argsort(-w[z], kind='stable')
        for j, k in enumerate(K_tr):
            layer = layer_masks(m, k); b = max(f[layer])
            out['score'].append(b - f[mask_of(rank[:k])])
            out['value'].append(b - f[max(layer, key=lambda s: fh[z, s])])
            out['direct'].append(b - f[int(masks_from_logits(dl[z, j], k))])
    if not use_score:
        out.pop('score')
    return {k: float(np.mean(v)) for k, v in out.items()}


def main(a):
    torch.set_num_threads(1)
    man, rows, splits = load(a.data)
    m = rows[0]['m']
    Y = np.asarray([r['values'] for r in rows], dtype=np.float64)
    regimes = {'all': (list(range(1, m)), list(range(1, m))), 'holdout': ([2, 4, 6], [3, 5, 7])}
    report = dict(status='RUNNING', data=str(Path(a.data).resolve()), table_sha256=man['table_sha256'],
                  evidence_class='OFFLINE SELECTOR SCREEN on frozen MP2; ceiling features are ORACLE',
                  results={})
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    t0 = time.perf_counter()
    for fs in a.feature_sets:
        X = features(rows, fs)
        for reg in a.regimes:
            K_tr, K_ev = regimes[reg]
            use_score = reg == 'all'
            per_seed = []
            for seed in a.seeds:
                nets, xt, masks = train_one(X, Y, splits, m, K_tr, seed, a.epochs, a.hidden, use_score)
                bud_ev = torch.tensor(K_ev, dtype=torch.float32)[:, None] / m
                res = {sp: regrets(rows, splits[sp], Y, nets, xt, masks, bud_ev, K_ev, m, use_score)
                       for sp in ('test', 'train')}
                per_seed.append(res)
                print(f'[{time.perf_counter() - t0:.0f}s] {fs}/{reg} seed {seed}: test '
                      + json.dumps({k: round(v, 2) for k, v in res['test'].items()}), flush=True)
            summ = {}
            for sp in ('test', 'train'):
                summ[sp] = {meth: dict(mean=float(np.mean([s[sp][meth] for s in per_seed])),
                                       by_seed=[round(s[sp][meth], 3) for s in per_seed])
                            for meth in per_seed[0][sp]}
            report['results'][f'{fs}/{reg}'] = dict(K_train=K_tr, K_eval=K_ev, **summ)
    report['status'] = 'COMPLETE'; report['seconds'] = time.perf_counter() - t0
    report['config'] = dict(epochs=a.epochs, hidden=a.hidden, seeds=a.seeds)
    (out / 'report.json').write_text(json.dumps(report, indent=1, allow_nan=False))
    print('COMPLETE', out / 'report.json', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--data', required=True); p.add_argument('--out', required=True)
    p.add_argument('--epochs', type=int, default=150); p.add_argument('--hidden', type=int, default=64)
    p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2])
    p.add_argument('--feature-sets', nargs='+', default=['public', 'bid', 'ceiling'])
    p.add_argument('--regimes', nargs='+', default=['all', 'holdout'])
    main(p.parse_args())
