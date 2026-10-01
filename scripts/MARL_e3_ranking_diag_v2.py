#!/usr/bin/env python3
"""Ranking diagnostic v2 (independent recheck 18:50; v1 MARL_e3_ranking_diag.py and its JSON are kept).

v1 scored the critic STRICTLY (a predicted tie = 0) but the fewer-edits rule with half credit for ties, so the two
were not comparable, and a strict score must not be compared with 0.5.  v2 uses ONE metric for every scorer:
    pair_acc = P(pred_diff > 0 | true_diff > 0) + 0.5 * P(pred_diff == 0 | true_diff > 0)
(exact ties only; no epsilon), and reports the predicted-tie fraction.  Self-test before any data (abort on
failure): an all-tie predictor scores 0.5, a perfect one 1, a fully reversed one 0.
Per checkpoint and split (TRAIN = every train state, SELECT, DEV): overall, equal-edit-size and |true diff| >= 5
pair accuracies for the critic and for the fewer-edits rule, on the SAME eligible candidates (the checkpoint's own
feasible set, as the trainer: +84 B minus 10 B for bid arms), macro-averaged over states.  Uncertainty: bootstrap
over TRAFFIC SEEDS (every load and snapshot of a seed together; the arm's checkpoints averaged within a state), for
the critic, the rule, and critic minus rule.  State-level rows, checkpoint sha256 and source sha256 are saved.
Diagnostic of ordering only: a good pair accuracy is not a positive selected gain (the fewer-edits rule used as a
selector would always keep the prefix).
"""
from __future__ import annotations
import argparse, glob, hashlib, json, sys
from collections import defaultdict
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load, Net
from scripts.MARL_e3_selector_diag_v2 import predictions
from models.marl_e3_response import RespNet

SOURCES = ['scripts/MARL_e3_ranking_diag_v2.py', 'scripts/MARL_e3_selector_diag_v2.py', 'scripts/MARL_e3_selector_train.py', 'models/marl_e3_response.py']


def pair_acc(pred, y, mask=None):
    """Tie-half pair accuracy over pairs with y_a > y_b (optionally restricted by mask); returns (acc, tie_frac, n)."""
    dy = y[:, None] - y[None, :]; dp = pred[:, None] - pred[None, :]; m = dy > 0
    if mask is not None:
        m = m & mask
    n = int(m.sum())
    if n == 0:
        return np.nan, np.nan, 0
    return float((dp[m] > 0).mean() + 0.5 * (dp[m] == 0).mean()), float((dp[m] == 0).mean()), n


def selftest():
    y = np.array([0.0, 1.0, 2.0, 5.0])
    assert pair_acc(np.zeros(4), y)[0] == 0.5, 'all-tie predictor must score 0.5'
    assert pair_acc(y.copy(), y)[0] == 1.0, 'perfect predictor must score 1'
    assert pair_acc(-y, y)[0] == 0.0, 'reversed predictor must score 0'
    print('selftest PASS (all-tie 0.5, perfect 1, reversed 0)', flush=True)


def n_repl(c, P):
    return sum(len(set(s) - set(p)) for s, p in zip(c['sets'], P['sets']))


def boot(vals, keys, B=5000, seed=0):
    by = defaultdict(list)
    for v, k in zip(vals, keys):
        if not np.isnan(v):
            by[k].append(v)
    K = sorted(by); rng = np.random.default_rng(seed)
    out = [np.mean(np.concatenate([by[K[i]] for i in rng.integers(0, len(K), len(K))])) for _ in range(B)]
    return [round(float(x), 4) for x in np.quantile(out, [0.025, 0.975])]


def main(a):
    selftest(); torch.set_num_threads(a.threads)
    D = Path(a.actor_dir); h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    splits = {sp: load([x for x in sorted(glob.glob(str(D / pat))) if Path(x).is_dir()])[0]
              for sp, pat in (('train', 'labels_train_*'), ('select', 'labels_select'), ('dev', 'labels_dev'))}
    files = sorted(glob.glob(str(D / a.models)))
    if not files:
        raise SystemExit('no checkpoints')
    rows = defaultdict(list)                       # (split, state index) -> per-checkpoint metrics
    ck_info = []
    for mf in files:
        meta = torch.load(mf, weights_only=False); net = Net(*meta['dims'], meta['hidden']); net.load_state_dict(meta['state']); net.eval(); hn = None
        if meta.get('resp'):
            hn = RespNet(); hn.load_state_dict(meta['head']['state']); hn.eval()
        ck_info.append(dict(model=str(mf), sha256=hashlib.sha256(Path(mf).read_bytes()).hexdigest()))
        for sp, S in splits.items():
            for k, st in enumerate(S):
                an, y, feas, _ = predictions(meta, net, hn, st); ok = feas.copy(); ok[0] = True
                P = st['cands'][0]; nr = np.array([n_repl(c, P) for c in st['cands']], float)[ok]; a_, y_ = an[ok], y[ok]
                eq = (nr[:, None] - nr[None, :]) == 0; big = (y_[:, None] - y_[None, :]) >= 5
                c_all, tie, npair = pair_acc(a_, y_); c_eq = pair_acc(a_, y_, eq)[0]; c_big = pair_acc(a_, y_, big)[0]
                r_all = pair_acc(-nr, y_)[0]; r_eq = 0.5 if not np.isnan(c_eq) else np.nan
                rows[(sp, k)].append(dict(critic=c_all, critic_equal_size=c_eq, critic_big=c_big, tie_frac=tie, rule=r_all, rule_equal_size=r_eq, pairs=npair))
    out = dict(actor_dir=str(D), models=ck_info, source_hashes=h0, metric='tie-half pair accuracy', splits={})
    for sp, S in splits.items():
        seeds = [str(st['traffic_seed']) for st in S]; per = {}
        for key in ('critic', 'critic_equal_size', 'critic_big', 'tie_frac', 'rule'):
            v = [np.nanmean([r[key] for r in rows[(sp, k)]]) for k in range(len(S))]
            per[key] = dict(mean=round(float(np.nanmean(v)), 4), ci_traffic_seed=boot(v, seeds))
        d = [np.nanmean([r['critic'] for r in rows[(sp, k)]]) - np.nanmean([r['rule'] for r in rows[(sp, k)]]) for k in range(len(S))]
        per['critic_minus_rule'] = dict(mean=round(float(np.nanmean(d)), 4), ci_traffic_seed=boot(d, seeds))
        per['per_checkpoint_critic'] = [round(float(np.nanmean([rows[(sp, k)][i]['critic'] for k in range(len(S))])), 4) for i in range(len(files))]
        per['states'] = len(S)
        out['splits'][sp] = per
        out.setdefault('state_rows', {})[sp] = [dict(episode=st['episode_id'], t=st['t'], checkpoints=rows[(sp, k)]) for k, st in enumerate(S)]
        print(f'{sp:6s} ({len(S)} states): critic {per["critic"]["mean"]:.4f} {per["critic"]["ci_traffic_seed"]} per-ckpt {per["per_checkpoint_critic"]} | '
              f'equal-size {per["critic_equal_size"]["mean"]:.4f} {per["critic_equal_size"]["ci_traffic_seed"]} | big {per["critic_big"]["mean"]:.4f} | '
              f'ties {per["tie_frac"]["mean"]:.3f} | fewer-edits rule {per["rule"]["mean"]:.4f} | critic-rule {per["critic_minus_rule"]["mean"]:+.4f} {per["critic_minus_rule"]["ci_traffic_seed"]}', flush=True)
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    Path(a.out).write_text(json.dumps(out, default=float))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actor-dir', required=True); p.add_argument('--models', default='selectors_v3/model_legal_bid_resp_s*.pt')
    p.add_argument('--threads', type=int, default=1); p.add_argument('--out', required=True)
    main(p.parse_args())
