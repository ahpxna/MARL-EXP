#!/usr/bin/env python3
"""Cheap checks v3 trainer: the v2 tables, with the fixes of MARL_CHEAP_V2_INDEPENDENT_AUDIT.

The v2 trainer (scripts/MARL_cheap_checks_v2_train.py) is kept unchanged as the producer of
its report.  Changes here, each tied to an audit finding:
  * condition names: `fresh_bid_ablation` (was `bid`: an OFFLINE feature ablation; the bids
    are NOT transmitted in the live protocol and NOT charged) and
    `privileged_current_summaries` (was `ceiling`: phase + approach totals of every agent,
    NOT the simulator state, NOT an information ceiling)                    [audit §4, §5]
  * targets are centred within each (context, subset-size) layer over the TRAINED sizes only,
    and the target scale is computed from those centred training labels; no label of a
    held-out size enters any statistic, loss or selection (tested)            [audit §6]
  * both regimes are also evaluated on the SAME held-out budgets k = 3,5,7    [audit §6]
  * two prepared priorities from the critic: sum-over-k chain and worst-k (minimax) chain [§7]
  * every decision is saved (feature set, regime, seed, split, episode, t, k, method, set,
    value, regret); per-k and per-episode tables are derived from it; the report records
    source hashes                                                             [audit §7]
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

SOURCES = ['scripts/MARL_cheap_checks_v3_train.py', 'scripts/MARL_cheap_pilot.py',
           'models/marl_revision_selector.py', 'models/marl_screening.py']
ALIASES = {'bid': 'fresh_bid_ablation', 'ceiling': 'privileged_current_summaries'}


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
    kind = ALIASES.get(kind, kind)
    out = []
    for r in rows:
        x = list(r['features'])
        if kind == 'fresh_bid_ablation':
            x += [b / 255.0 for b in r['bids']]
        elif kind == 'privileged_current_summaries':
            x += list(r['fresh_features'])
        elif kind != 'public':
            raise ValueError(kind)
        out.append(x)
    return np.asarray(out, dtype=np.float32)


def centred_targets(Y, m, sizes):
    """Within-layer centred values for the given subset sizes only; other columns are NaN."""
    T = np.full_like(Y, np.nan)
    for k in sizes:
        ix = layer_masks(m, k)
        T[:, ix] = Y[:, ix] - Y[:, ix].mean(1, keepdims=True)
    return T


def chain_from(fh, m, agg):
    best = {k: max(fh[s] for s in layer_masks(m, k)) for k in range(1, m)}
    dp = {0: (0.0, [])}
    for k in range(1, m):
        nd = {}
        for C0, (v0, path) in dp.items():
            for i in range(m):
                if not (C0 >> i) & 1:
                    C = C0 | (1 << i); r = best[k] - fh[C]
                    val = v0 + r if agg == 'sum' else max(v0, r)
                    if C not in nd or val < nd[C][0]:
                        nd[C] = (val, path + [i])
        dp = nd
    _, path = min(dp.values(), key=lambda t: t[0])
    return tuple(path + [i for i in range(m) if i not in path])


def train_one(X, Y, splits, m, K_tr, seed, epochs, hidden, use_score):
    torch.manual_seed(seed); rng = np.random.default_rng(seed)
    tr, va = splits['train'], splits['val']
    mean = X[tr].mean(0); std = X[tr].std(0); std[std < 1e-6] = 1
    xt = torch.as_tensor((X - mean) / std, dtype=torch.float32)
    T = centred_targets(Y, m, K_tr)
    cols = np.concatenate([layer_masks(m, k) for k in K_tr])
    scale = max(float(np.std(T[np.ix_(tr, cols)])), 1.0)
    Tz = np.nan_to_num(T / scale, nan=0.0)
    yt = torch.as_tensor(Tz, dtype=torch.float32)
    masks = torch.tensor([[(s >> i) & 1 for i in range(m)] for s in range(1 << m)], dtype=torch.float32)
    size = masks.sum(1).long()
    bud_tr = torch.tensor(K_tr, dtype=torch.float32)[:, None] / m
    layer_ok = size[None, :] == torch.tensor(K_tr)[:, None]
    lay_idx = [torch.as_tensor(layer_masks(m, k)) for k in K_tr]
    singleton = torch.tensor([1 << i for i in range(m)])
    nets = {k: SelectorNet(X.shape[1], m, k, hidden) for k in ('score', 'value', 'direct')}
    opts = {k: torch.optim.Adam(n.parameters(), lr=0.003) for k, n in nets.items()}
    best = {k: float('inf') for k in nets}; saved = {}

    def centred(v):
        return torch.cat([v[:, ix] - v[:, ix].mean(1, keepdim=True) for ix in lay_idx], 1)

    ycat = torch.cat([yt[:, ix] for ix in lay_idx], 1)
    for epoch in range(epochs):
        for b in np.array_split(rng.permutation(tr), max(1, (len(tr) + 7) // 8)):
            xb = xt[b]
            losses = {}
            if use_score:
                losses['score'] = ((nets['score'](xb) - yt[b][:, singleton]) ** 2).mean()
            losses['value'] = ((centred(nets['value'](xb, masks)) - ycat[b]) ** 2).mean()
            lg = nets['direct'](xb, bud_tr)
            sl = torch.einsum('bkm,nm->bkn', lg, masks).masked_fill(~layer_ok[None], -torch.inf)
            losses['direct'] = -(sl.softmax(-1) * yt[b][:, None, :]).sum(-1).mean()
            for k, l in losses.items():
                opts[k].zero_grad(); l.backward(); opts[k].step()
        if epoch % 10 == 0 or epoch == epochs - 1:
            for k, v in val_regret(Y, va, nets, xt, masks, bud_tr, K_tr, m, use_score).items():
                if v < best[k]:
                    best[k] = v; saved[k] = copy.deepcopy(nets[k].state_dict())
    for k, n in nets.items():
        if k in saved:
            n.load_state_dict(saved[k])
        n.eval()
    return nets, xt, masks, dict(scale=scale)


def val_regret(Y, va, nets, xt, masks, bud_tr, K_tr, m, use_score):
    with torch.no_grad():
        w = nets['score'](xt[va]).numpy(); fh = nets['value'](xt[va], masks).numpy()
        dl = nets['direct'](xt[va], bud_tr).numpy()
    out = {'score': [], 'value': [], 'direct': []}
    for z, i in enumerate(va):
        f = Y[i]; rank = np.argsort(-w[z], kind='stable')
        for j, k in enumerate(K_tr):
            layer = layer_masks(m, k); b = max(f[layer])
            out['score'].append(b - f[mask_of(rank[:k])])
            out['value'].append(b - f[max(layer, key=lambda s: fh[z, s])])
            out['direct'].append(b - f[int(masks_from_logits(dl[z, j], k))])
    if not use_score:
        out.pop('score')
    return {k: float(np.mean(v)) for k, v in out.items()}


def decisions(rows, idx, Y, nets, xt, masks, K_ev, m, use_score):
    bud = torch.tensor(K_ev, dtype=torch.float32)[:, None] / m
    with torch.no_grad():
        w = nets['score'](xt[idx]).numpy(); fh = nets['value'](xt[idx], masks).numpy()
        dl = nets['direct'](xt[idx], bud).numpy()
    out = []
    for z, i in enumerate(idx):
        f = Y[i]; row = rows[i]
        cs, cm = chain_from(fh[z], m, 'sum'), chain_from(fh[z], m, 'max')
        rank = tuple(int(a) for a in np.argsort(-w[z], kind='stable'))
        for j, k in enumerate(K_ev):
            layer = layer_masks(m, k); best = float(max(f[layer]))
            c1 = [mask_of(s) for s in reachable_sets(cs, k, 1)]
            ch = dict(cached_queue_prefix=mask_of(row['cached_queue_ranking'][:k]),
                      critic_chain_sum=mask_of(cs[:k]), critic_chain_minimax=mask_of(cm[:k]),
                      critic_chain_sum_R1=max(c1, key=lambda s: fh[z, s]),
                      critic_per_budget_table=max(layer, key=lambda s: fh[z, s]),
                      direct_budget_network=int(masks_from_logits(dl[z, j], k)),
                      oracle_R1_of_chain_sum=max(c1, key=lambda s: f[s]))
            if use_score:
                s1 = [mask_of(s) for s in reachable_sets(rank, k, 1)]
                ch.update(learned_score_prefix=mask_of(rank[:k]),
                          learned_score_R1_by_critic=max(s1, key=lambda s: fh[z, s]))
            for meth, s in ch.items():
                out.append(dict(episode_id=row['episode_id'], t=row['t'], k=k, method=meth,
                                selected_mask=int(s), value=float(f[s]), regret=best - float(f[s])))
    return out


def summarise(recs):
    by = {}
    for r in recs:
        by.setdefault(r['method'], {}).setdefault(r['episode_id'], []).append(r['regret'])
    return {m: float(np.mean([np.mean(v) for v in e.values()])) for m, e in by.items()}


def main(a):
    torch.set_num_threads(1)
    man, rows, splits = load(a.data)
    m = rows[0]['m']
    Y = np.asarray([r['values'] for r in rows], dtype=np.float64)
    regimes = {'all': list(range(1, m)), 'holdout': [2, 4, 6]}
    evals = {'all_k': list(range(1, m)), 'heldout_k_357': [3, 5, 7]}
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    hashes = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    report = dict(status='RUNNING', data=str(Path(a.data).resolve()), table_sha256=man['table_sha256'],
                  source_hashes=hashes, evidence_class='OFFLINE SELECTOR SCREEN on frozen MP2 held-phase values',
                  condition_notes={'fresh_bid_ablation': 'offline feature ablation; bids not transmitted, not charged',
                                   'privileged_current_summaries': 'phase and approach totals of every agent; not full state'},
                  results={})
    t0 = time.perf_counter()
    with gzip.open(out / 'decisions.jsonl.gz', 'wt') as dec:
        for fs in a.feature_sets:
            fs = ALIASES.get(fs, fs); X = features(rows, fs)
            for reg in a.regimes:
                K_tr = regimes[reg]; use_score = reg == 'all'
                res = {}
                for seed in a.seeds:
                    nets, xt, masks, info = train_one(X, Y, splits, m, K_tr, seed, a.epochs, a.hidden, use_score)
                    for ev, K_ev in evals.items():
                        if reg == 'holdout' and ev == 'all_k':
                            continue
                        for sp in ('test', 'train'):
                            recs = decisions(rows, splits[sp], Y, nets, xt, masks, K_ev, m, use_score)
                            for r in recs:
                                r.update(feature_set=fs, regime=reg, seed=seed, split=sp, eval=ev)
                                dec.write(json.dumps(r) + '\n')
                            res.setdefault(f'{ev}/{sp}', []).append(summarise(recs))
                    print(f'[{time.perf_counter() - t0:.0f}s] {fs}/{reg} seed {seed} scale {info["scale"]:.4f}', flush=True)
                report['results'][f'{fs}/{reg}'] = {
                    key: {meth: dict(mean=float(np.mean([s[meth] for s in lst])),
                                     by_seed=[round(s[meth], 3) for s in lst]) for meth in lst[0]}
                    for key, lst in res.items()}
    if hashes != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    report.update(status='COMPLETE', seconds=time.perf_counter() - t0,
                  decisions_sha256=hashlib.sha256((out / 'decisions.jsonl.gz').read_bytes()).hexdigest(),
                  config=dict(epochs=a.epochs, hidden=a.hidden, seeds=a.seeds))
    (out / 'report.json').write_text(json.dumps(report, indent=1, allow_nan=False))
    print('COMPLETE', out / 'report.json', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--data', required=True); p.add_argument('--out', required=True)
    p.add_argument('--epochs', type=int, default=150); p.add_argument('--hidden', type=int, default=64)
    p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2])
    p.add_argument('--feature-sets', nargs='+',
                   default=['public', 'fresh_bid_ablation', 'privileged_current_summaries'])
    p.add_argument('--regimes', nargs='+', default=['all', 'holdout'])
    main(p.parse_args())
