#!/usr/bin/env python3
"""Mitigation M-C DEVELOPMENT screen: receiver-local REQUEST bids (MARL_hetero_bid_replay.py).

Same splits and evaluation as MARL_hetero_mitigation_dev.py (fit 301-364, select 401-408, report
501-508 as DEVELOPMENT; the B1 test panel is opened, so nothing here is confirmatory).

Selectors, all charged inside the SAME total cap:
  rule_request        NO learning.  h(S) = sum over edited receivers i of
                        +w(gap_i) if S_i adds i's requested sender, else -0.5,
                      w = 1 (gap < 1), 0.5 (gap < 2), 0.25 otherwise; anchored at the prefix (0);
                      no-edit threshold tau selected on the select split.  Fixed bid: 1 B per
                      receiver (4-bit sender, 4-bit gap) + 1 B header = 10 B.
  rule_request_sparse the same rule; only receivers with gap < 2 bid: 2 B presence bitmap +
                      1 B per bidding receiver + 1 B header (actual bytes, per group); receivers
                      that do not bid are never edited.
  mlp_bid_request     the MARL_hetero_mitigation_dev trainer (imported, same hyper-parameters) on
                      z, K, candidate mask + one-hot requested sender and quantised gap; 10 B.
The weights of the rule were fixed BEFORE this script was run, from the single-swap gain table in
FULL_CORPUS_AUDIT §23.11 (computed on all B1 splits: a development choice, stated as such).
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import scripts.MARL_hetero_mitigation_dev as md
from scripts.MARL_hetero_diag_train_v2 import choose, outcome, summarise, anchor

SOURCES = ['scripts/MARL_hetero_bid_request_dev.py', 'scripts/MARL_hetero_mitigation_dev.py',
           'scripts/MARL_hetero_bid_replay.py', 'scripts/MARL_hetero_diag_train_v2.py']
FIXED_BID = 10
TOTALS = [28, 56, 84, None]


def w_of(gap):
    return 1.0 if gap < 1 else (0.5 if gap < 2 else 0.25)


def attach_bids(G, run):
    B = {}
    for d in sorted(x for x in run.glob('bid2_*') if x.is_dir()):
        for l in gzip.open(d / 'bid2_diag.jsonl.gz', 'rt'):
            r = json.loads(l); B[(r['episode_id'], r['t'])] = r['bid']
    # md.build keeps group order per record; recover (episode, t) by re-reading the labels order
    k = 0
    for lab in sorted(run.glob('labels_*')):
        for l in gzip.open(lab / 'labels.jsonl.gz', 'rt'):
            r = json.loads(l)
            for _ in r['groups']:
                g = G[k]; k += 1
                if g['ep'] != r['episode_id']:
                    raise AssertionError('order mismatch')
                g['bid2'] = B[(r['episode_id'], r['t'])]
    if k != len(G):
        raise AssertionError('group count mismatch')


def rule_scores(g, sparse):
    m = g['m']; bid = g['bid2']; C = g['C']
    added = g['masks'].reshape(C, m, m).astype(bool) & ~g['masks'][g['ev']['ip']].reshape(m, m).astype(bool)[None]
    h = np.zeros(C)
    for i in range(m):
        e = g['edited'][:, i]
        if not e.any():
            continue
        rq = bid[i]['req']
        hit = added[:, i, rq] if rq >= 0 else np.zeros(C, bool)
        val = np.where(hit, w_of(bid[i]['gap']), -0.5)
        if sparse and bid[i]['gap'] >= 2:
            val = np.full(C, -np.inf)                      # a silent receiver is never edited
        h += np.where(e, val, 0.0)
    h[g['ev']['ip']] = 0.0
    return h


def sparse_bytes(g):
    return 2 + 1 + sum(1 for b in g['bid2'] if b['gap'] < 2)


def eval_rule(groups_sel, groups_dev, sparse):
    res = {}
    anch_s = [rule_scores(g, sparse) for g in groups_sel]; anch_d = [rule_scores(g, sparse) for g in groups_dev]
    for total in TOTALS:
        key = 'none' if total is None else f'+{total}'
        cxs = lambda gs: [None if total is None else total - (sparse_bytes(g) if sparse else FIXED_BID) for g in gs]
        cs, cd = cxs(groups_sel), cxs(groups_dev)
        pos = np.concatenate([a[np.isfinite(a) & (a > 0)] for a in anch_s])
        grid = [0.0] + (list(np.quantile(pos, [0.1, 0.25, 0.5, 0.75, 0.9])) if len(pos) else []) + [np.inf]
        row = {}
        for pol in ('repair_R1', 'direct'):
            best_t, best_v = None, -np.inf
            for t in grid:
                v = np.mean([outcome(g['ev'], choose(g['ev'], a, c, pol == 'repair_R1', t))['gain']
                             for g, a, c in zip(groups_sel, anch_s, cs)])
                if v > best_v + 1e-12:
                    best_t, best_v = t, v
            o = [outcome(g['ev'], choose(g['ev'], a, c, pol == 'repair_R1', best_t)) for g, a, c in zip(groups_dev, anch_d, cd)]
            row[pol] = dict(summary=summarise(o), tau=None if np.isinf(best_t) else float(best_t), select_metric=best_v,
                            gains=[x['gain'] for x in o], eps=[x['ep'] for x in o], chosen=[x['chosen'] for x in o])
        o = [outcome(g['ev'], choose(g['ev'], g['ev']['delta'].astype(float), c, True, 0.0)) for g, c in zip(groups_dev, cd)]
        row['oracle_R1'] = dict(summary=summarise(o), gains=[x['gain'] for x in o])
        row['mean_bid_bytes'] = float(np.mean([sparse_bytes(g) if sparse else FIXED_BID for g in groups_dev]))
        res[key] = row
    return res


def patched_features(g, learner):
    if learner != 'mlp_bid_request':
        return _orig_features(g, learner)
    m = g['m']
    req = np.zeros((m, m + 1), np.float32)
    for i, b in enumerate(g['bid2']):
        req[i, b['req'] if b['req'] >= 0 else m] = 1
    gq = np.asarray([min(15, round(b['gap'])) / 15 for b in g['bid2']], np.float32)
    ctx = np.concatenate([g['ctx_pub'], req.reshape(-1), gq]).astype(np.float32)
    return ctx, g['masks'].astype(np.float32)


_orig_features = md.features


def main(a):
    run = Path(a.run); out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    t0 = time.perf_counter()
    G = md.build(run); attach_bids(G, run)
    sel = [g for g in G if g['split'] == 'select']; dev = [g for g in G if g['split'] == 'test']
    report = {}
    for name, sparse in (('rule_request', False), ('rule_request_sparse', True)):
        report[name] = eval_rule(sel, dev, sparse)
        r = report[name]
        print(f'[{time.perf_counter() - t0:.0f}s] {name}: ' + ' | '.join(
            f'{k} R1 {v["repair_R1"]["summary"]["gain"]:+.3f} dir {v["direct"]["summary"]["gain"]:+.3f} '
            f'orc {v["oracle_R1"]["summary"]["gain"]:+.2f} bid {v["mean_bid_bytes"]:.1f}B' for k, v in r.items()), flush=True)
    tmp = out / '.rules.json'; tmp.write_text(json.dumps(report, default=float)); os.replace(tmp, out / 'rules.json')
    if a.learned:
        md.features = patched_features; md.BID_BYTES['mlp_bid_request'] = FIXED_BID
        for s in a.seeds:
            b = md.run_job(G, 'mlp_bid_request', s, out, a.epochs, a.threads)
            r = b['results']['mlp_bid_request']
            print(f'[{time.perf_counter() - t0:.0f}s] mlp_bid_request s{s}: ' + ' | '.join(
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
