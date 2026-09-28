#!/usr/bin/env python3
"""Mitigation M-D DEVELOPMENT screen: 1-byte receiver TOP-2 bids + scheduler-side structure.

Inputs: MARL_hetero_bid_replay_v2.py (bid3_*): receiver bid (p1, p2, gapbin) = 1 B, the scheduler's
coefficients c[i][j] (public topology + known MP2 at the bid's p1, p2) and the receiver-cache ages
(legal mirror).  Per edited receiver i of a candidate S the structural refresh score is
    s_i(S) = sum_{b added} |c_ib| st(age_ib) - sum_{d dropped} |c_id| st(age_id),
    st(a) = 10 if never heard else 1 + a/10.
Selectors (bytes charged inside the SAME total cap; splits as MARL_hetero_mitigation_dev.py:
fit 301-364, select 401-408, DEVELOPMENT report 501-508, opened):
  rule_top2          h(S) = sum_{edited i} T[gapbin_i, sbin(s_i)], T = mean single-receiver
                     one-swap gain on the TRAIN split only (4 gap bins x 5 score bins); prefix 0;
                     tau on the select split.  Bid 9 B + 1 B header = 10 B.
  rule_top2_sparse   the same; only receivers with gapbin <= 1 bid (2 B bitmap + 1 B each +
                     1 B header, actual per group); silent receivers are never edited.
  mlp_top2           the imported trainer on z, K, one-hot (p1, p2, gapbin) per receiver, and per
                     candidate the mask, s_i and edited flags.  10 B.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_hetero_mitigation_dev as md
from scripts.MARL_hetero_diag_train_v2 import choose, outcome, summarise

SOURCES = ['scripts/MARL_hetero_bid_top2_dev.py', 'scripts/MARL_hetero_mitigation_dev.py',
           'scripts/MARL_hetero_bid_replay_v2.py', 'scripts/MARL_hetero_diag_train_v2.py']
FIXED_BID = 10
TOTALS = [28, 56, 84, None]
SBINS = [-np.inf, -1e-9, 1e-9, 2.0, 5.0, np.inf]          # (<0), 0, (0,2], (2,5], (5,inf)


def st(a):
    return 10.0 if a < 0 else 1.0 + a / 10.0


def attach(G, run):
    B = {}
    for d in sorted(x for x in run.glob('bid3_*') if x.is_dir()):
        for l in gzip.open(d / 'bid3_diag.jsonl.gz', 'rt'):
            r = json.loads(l); B[(r['episode_id'], r['t'])] = r['bid']
    k = 0
    for lab in sorted(run.glob('labels_*')):
        for l in gzip.open(lab / 'labels.jsonl.gz', 'rt'):
            r = json.loads(l)
            for _ in r['groups']:
                g = G[k]; k += 1
                if g['ep'] != r['episode_id']:
                    raise AssertionError('order mismatch')
                bid = B[(r['episode_id'], r['t'])]; m = g['m']
                W = np.array([[abs(b['c'][j]) * st(b['age'][j]) for j in range(m)] for b in bid])
                M = g['masks'].reshape(g['C'], m, m).astype(bool); MP = M[g['ev']['ip']]
                add = M & ~MP[None]; drop = MP[None] & ~M
                g['s'] = (add * W[None]).sum(2) - (drop * W[None]).sum(2)
                g['gapbin'] = np.array([b['gapbin'] for b in bid])
                g['top2'] = np.concatenate([np.concatenate([md.onehot8(b['p1']), md.onehot8(b['p2']),
                                                            np.eye(4, dtype=np.float32)[b['gapbin']]]) for b in bid])
    if k != len(G):
        raise AssertionError('group count mismatch')


def sbin(x):
    return np.digitize(x, SBINS[1:-1])


def fit_table(fit):
    S = np.zeros((4, 5)); N = np.zeros((4, 5))
    for g in fit:
        ed = g['edited']; one = ed.sum(1) == 1
        for c in np.nonzero(one)[0]:
            i = int(np.nonzero(ed[c])[0][0])
            S[g['gapbin'][i], sbin(g['s'][c, i])] += g['ev']['delta'][c]; N[g['gapbin'][i], sbin(g['s'][c, i])] += 1
    return np.where(N > 0, S / np.maximum(N, 1), 0.0), N


def rule_scores(g, T, sparse):
    h = np.zeros(g['C'])
    for i in range(g['m']):
        e = g['edited'][:, i]
        if not e.any():
            continue
        v = T[g['gapbin'][i], sbin(g['s'][:, i])]
        if sparse and g['gapbin'][i] > 1:
            v = np.full(g['C'], -np.inf)
        h += np.where(e, v, 0.0)
    h[g['ev']['ip']] = 0.0
    return h


def sparse_bytes(g):
    return 2 + 1 + int((g['gapbin'] <= 1).sum())


def eval_rule(sel, dev, T, sparse):
    res = {}
    As = [rule_scores(g, T, sparse) for g in sel]; Ad = [rule_scores(g, T, sparse) for g in dev]
    for total in TOTALS:
        key = 'none' if total is None else f'+{total}'
        cap = lambda g: None if total is None else total - (sparse_bytes(g) if sparse else FIXED_BID)
        pos = np.concatenate([a[np.isfinite(a) & (a > 0)] for a in As])
        grid = [0.0] + (list(np.quantile(pos, [0.1, 0.25, 0.5, 0.75, 0.9])) if len(pos) else []) + [np.inf]
        row = {}
        for pol in ('repair_R1', 'direct'):
            bt, bv = None, -np.inf
            for t in grid:
                v = np.mean([outcome(g['ev'], choose(g['ev'], a, cap(g), pol == 'repair_R1', t))['gain'] for g, a in zip(sel, As)])
                if v > bv + 1e-12:
                    bt, bv = t, v
            o = [outcome(g['ev'], choose(g['ev'], a, cap(g), pol == 'repair_R1', bt)) for g, a in zip(dev, Ad)]
            row[pol] = dict(summary=summarise(o), tau=None if np.isinf(bt) else float(bt), select_metric=bv,
                            gains=[x['gain'] for x in o], eps=[x['ep'] for x in o], chosen=[x['chosen'] for x in o])
        o = [outcome(g['ev'], choose(g['ev'], g['ev']['delta'].astype(float), cap(g), True, 0.0)) for g in dev]
        row['oracle_R1'] = dict(summary=summarise(o), gains=[x['gain'] for x in o])
        row['mean_bid_bytes'] = float(np.mean([sparse_bytes(g) if sparse else FIXED_BID for g in dev]))
        res[key] = row
    return res


_orig = md.features


def feats(g, learner):
    if learner != 'mlp_top2':
        return _orig(g, learner)
    ctx = np.concatenate([g['ctx_pub'], g['top2']]).astype(np.float32)
    cand = np.concatenate([g['masks'].astype(np.float32), np.clip(g['s'], -30, 30).astype(np.float32) / 10,
                           g['edited'].astype(np.float32)], 1)
    return ctx, cand


def main(a):
    run = Path(a.run); out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    t0 = time.perf_counter()
    G = md.build(run); attach(G, run)
    fit = [g for g in G if g['split'] == 'train']; sel = [g for g in G if g['split'] == 'select']
    dev = [g for g in G if g['split'] == 'test']
    T, N = fit_table(fit)
    print('table (train):', np.round(T, 3).tolist(), 'counts', N.astype(int).tolist(), flush=True)
    rep = dict(table=T.tolist(), counts=N.tolist())
    for name, sp in (('rule_top2', False), ('rule_top2_sparse', True)):
        rep[name] = eval_rule(sel, dev, T, sp)
        print(f'[{time.perf_counter() - t0:.0f}s] {name}: ' + ' | '.join(
            f'{k} R1 {v["repair_R1"]["summary"]["gain"]:+.3f} dir {v["direct"]["summary"]["gain"]:+.3f} '
            f'orc {v["oracle_R1"]["summary"]["gain"]:+.2f} bid {v["mean_bid_bytes"]:.1f}B'
            for k, v in rep[name].items()), flush=True)
    tmp = out / '.rules.json'; tmp.write_text(json.dumps(rep, default=float)); os.replace(tmp, out / 'rules.json')
    if a.learned:
        md.features = feats; md.BID_BYTES['mlp_top2'] = FIXED_BID
        for s in a.seeds:
            b = md.run_job(G, 'mlp_top2', s, out, a.epochs, a.threads)
            r = b['results']['mlp_top2']
            print(f'[{time.perf_counter() - t0:.0f}s] mlp_top2 s{s}: ' + ' | '.join(
                f'{k} R1 {v["repair_R1"]["summary"]["gain"]:+.3f} dir {v["direct"]["summary"]["gain"]:+.3f}'
                for k, v in r.items()), flush=True)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', run=str(run), source_hashes=h0,
        seconds=time.perf_counter() - t0, evidence_class='DEVELOPMENT screen on opened B1 data'), indent=1))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run', required=True); p.add_argument('--out', required=True)
    p.add_argument('--learned', action='store_true'); p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2])
    p.add_argument('--epochs', type=int, default=40); p.add_argument('--threads', type=int, default=3)
    main(p.parse_args())
