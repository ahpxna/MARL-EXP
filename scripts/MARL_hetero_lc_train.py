#!/usr/bin/env python3
"""B1 learning curve: fit / select / sealed test (research/marl_budget/PROTOCOL_B1_LEARNING_CURVE_20260927.md).

Learners, anchoring, tie rule, epoch/lambda/tau selection and the operating point are those of
MARL_hetero_diag_train_v2.py, IMPORTED unchanged.  What differs: the splits (train pool 301-364
nested by level N, select 401-408, test 501-508) and the sealed test evaluation after selection.
Several (labels, mirror) shard pairs are joined.  Jobs (level, learner, init seed) run in worker
processes with one torch thread each.
Self-checks (abort, nothing written): seed-disjoint splits; prefix delta == 0 in every group;
oracle_R1 gain >= 0 in every group; sources unchanged.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

SOURCES = ['scripts/MARL_hetero_lc_train.py', 'scripts/MARL_hetero_diag_train_v2.py',
           'scripts/MARL_hetero_diag_train.py', 'models/marl_hetero_selector.py',
           'research/marl_budget/PROTOCOL_B1_LEARNING_CURVE_20260927.md']
POOL = list(range(301, 365))
PRIMARY = 'mlp_history'
G = None


def hashes():
    return {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}


def load_all(pairs):
    from scripts.MARL_hetero_diag_train import load
    groups = []
    for lab, mir in pairs:
        groups += load(lab, mir)
    return groups


def init(pairs):
    global G
    import torch
    torch.set_num_threads(1)
    G = load_all(pairs)


def job(spec):
    import torch
    torch.set_num_threads(1)
    from scripts.MARL_hetero_diag_train import ridge_features
    from scripts.MARL_hetero_diag_train_v2 import feats, train_mlp, fit_ridge, evaluate, summarise
    level, learner, seed = spec
    fit = [g for g in G if g['split'] == 'train' and g['seed'] in POOL[:level]]
    sel = [g for g in G if g['split'] == 'select']
    test = [g for g in G if g['split'] == 'test']
    t0 = time.perf_counter()
    if learner.startswith('ridge'):
        hist = learner == 'ridge_edge_history'
        Xf = np.concatenate([ridge_features(g, hist) for g in fit]); Yf = np.concatenate([g['delta'] for g in fit])
        f, info, _ = fit_ridge(Xf, Yf, [ridge_features(g, hist) for g in sel], sel)
        sp = [f(ridge_features(g, hist)) for g in sel]; tp = [f(ridge_features(g, hist)) for g in test]
    else:
        kind = learner[len('mlp_'):]
        Xf = np.concatenate([feats(g, kind) for g in fit]).astype(np.float32)
        Yf = np.concatenate([g['delta'] for g in fit]).astype(np.float32)
        Xs = [feats(g, kind).astype(np.float32) for g in sel]; Xt = [feats(g, kind).astype(np.float32) for g in test]
        f, info, _ = train_mlp(Xf, Yf, Xs, sel, seed)
        sp = [f(x) for x in Xs]; tp = [f(x) for x in Xt]
    res, taus, _, _, marg = evaluate(test, sel, sp, tp)
    caps = {cap: {pol: summarise(o) for pol, o in d.items()} for cap, d in res.items()}
    op = res['+28']
    return dict(level=level, learner=learner, seed=seed, fit_groups=len(fit), selection=info,
                tau={k: (None if np.isinf(v) else float(v)) for k, v in taus.items()}, margins=marg, caps=caps,
                test_gain=[o['gain'] for o in op['repair_R1']], test_ep=[o['ep'] for o in op['repair_R1']],
                oracle_gain=[o['gain'] for o in op['oracle_R1']], seconds=time.perf_counter() - t0)


def cluster_boot(gain, ep, B, rng):
    eps = sorted(set(ep)); idx = {e: [i for i, x in enumerate(ep) if x == e] for e in eps}
    gain = np.asarray(gain, float); out = np.empty(B)
    for b in range(B):
        pick = rng.choice(len(eps), size=len(eps), replace=True)
        rows = np.concatenate([idx[eps[p]] for p in pick])
        out[b] = gain[rows].mean()
    return np.quantile(out, [0.025, 0.975]).tolist()


def verdict(results, level, learner, B, rng):
    rs = [r for r in results if r['level'] == level and r['learner'] == learner]
    if not rs:
        return None
    per_seed = [float(np.mean(r['test_gain'])) for r in rs]
    avg = np.mean([r['test_gain'] for r in rs], axis=0)
    ep = rs[0]['test_ep']; oracle = float(np.mean(rs[0]['oracle_gain']))
    lo, hi = cluster_boot(avg, ep, B, rng)
    c1 = all(x > 0 for x in per_seed); c2 = lo > 0; c3 = float(avg.mean()) >= 0.25 * oracle
    return dict(per_seed=per_seed, mean=float(avg.mean()), ci95=[lo, hi], oracle_R1=oracle,
                frac_of_oracle=float(avg.mean()) / oracle if oracle > 0 else None,
                c1_all_seeds_positive=c1, c2_ci_lower_positive=c2, c3_quarter_of_oracle=c3, PASS=bool(c1 and c2 and c3))


def main(a):
    pairs = [tuple(x.split(':')) for x in a.shards]
    h0 = hashes()
    groups = load_all(pairs)
    seeds = {s: {g['seed'] for g in groups if g['split'] == s} for s in ('train', 'select', 'test')}
    if seeds['train'] & seeds['select'] or seeds['train'] & seeds['test'] or seeds['select'] & seeds['test']:
        raise AssertionError(f'splits share seeds: {seeds}')
    if not seeds['train'] <= set(POOL):
        raise AssertionError('train seed outside the pool')
    for g in groups:
        if abs(float(g['delta'][g['ip']])) > 1e-12:
            raise AssertionError('prefix delta != 0')
    levels = [l for l in a.levels if l <= len(seeds['train'])]
    specs = [(l, lr, s) for l in levels for lr in a.learners for s in (a.seeds if lr.startswith('mlp') else [0])]
    print(f'{len(groups)} groups (train {len(seeds["train"])} seeds, select {len(seeds["select"])}, '
          f'test {len(seeds["test"])}); {len(specs)} jobs on {a.workers} workers', flush=True)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    t0 = time.perf_counter(); results = []
    specs.sort(key=lambda s: -s[0])                       # largest first
    with ProcessPoolExecutor(max_workers=a.workers, initializer=init, initargs=(pairs,)) as ex:
        for r in ex.map(job, specs):
            if any(x < -1e-9 for x in r['oracle_gain']):
                raise AssertionError('oracle_R1 gain < 0')
            results.append(r)
            print(f'[{time.perf_counter() - t0:.0f}s] N={r["level"]} {r["learner"]} seed {r["seed"]}: '
                  f'test gain {np.mean(r["test_gain"]):+.3f} (oracle {np.mean(r["oracle_gain"]):+.3f}), '
                  f'{r["seconds"]:.0f}s', flush=True)
    if hashes() != h0:
        raise RuntimeError('source changed during run')
    rng = np.random.default_rng(0)
    curves = {lr: {l: verdict(results, l, lr, a.boot, rng) for l in levels} for lr in a.learners}
    top = max(levels)
    primary = curves.get(PRIMARY, {}).get(top)
    ref = curves.get('mlp_joint_only', {}).get(top)
    (out / 'report.json').write_text(json.dumps(dict(
        status='COMPLETE', protocol='PROTOCOL_B1_LEARNING_CURVE_20260927', shards=pairs, source_hashes=h0,
        levels=levels, learners=a.learners, init_seeds=a.seeds, curves=curves,
        primary_at_top=primary, privileged_reference_at_top=ref,
        B1_PASS=(primary or {}).get('PASS') if top == 64 else None, top_level=top, jobs=results,
        seconds=time.perf_counter() - t0), indent=1, default=float))
    print('curves:', json.dumps({lr: {l: (v and dict(mean=round(v['mean'], 3), ci=[round(x, 3) for x in v['ci95']],
          frac=v['frac_of_oracle'] and round(v['frac_of_oracle'], 3), PASS=v['PASS'])) for l, v in c.items()}
          for lr, c in curves.items()}, indent=1), flush=True)
    print('B1_PASS at N=64:', (primary or {}).get('PASS') if top == 64 else 'n/a (not the full run)', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--shards', nargs='+', required=True, help='labels_dir:mirror_dir pairs')
    p.add_argument('--out', required=True)
    p.add_argument('--levels', type=int, nargs='+', default=[8, 16, 32, 64])
    p.add_argument('--learners', nargs='+', default=['mlp_history', 'mlp_public', 'ridge_edge_history', 'mlp_joint_only'])
    p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2])
    p.add_argument('--workers', type=int, default=5)
    p.add_argument('--boot', type=int, default=10000)
    main(p.parse_args())
