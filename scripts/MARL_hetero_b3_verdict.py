#!/usr/bin/env python3
"""B3 verdict (research/marl_budget/PROTOCOL_B3_CLOSED_LOOP_20260927.md), read-only on rows.json."""
from __future__ import annotations
import argparse, json
from collections import defaultdict
from pathlib import Path
import numpy as np


def boot(v, B=10000, seed=0):
    rng = np.random.default_rng(seed); v = np.asarray(v, float)
    return [float(x) for x in np.quantile([v[rng.integers(0, len(v), len(v))].mean() for _ in range(B)], [0.025, 0.975])]


def main(a):
    rows = json.loads((Path(a.run) / 'rows.json').read_text())
    by = defaultdict(dict)
    for r in rows:
        by[r['method']][r['episode']] = r
    eps = sorted(by['prefix'])
    def avg(prefix_name, key):
        ms = [m for m in by if m.startswith(prefix_name + '/')]
        return np.array([np.mean([by[m][e][key] for m in ms]) for e in eps]), ms
    q_bid, mb = avg('mlp_top2_joint', 'queue_sum'); q_ctl, mc = avg('ctrl_history', 'queue_sum')
    f_bid, _ = avg('mlp_top2_joint', 'finished'); f_ctl, _ = avg('ctrl_history', 'finished')
    b_bid, _ = avg('mlp_top2_joint', 'bytes'); b_ctl, _ = avg('ctrl_history', 'bytes')
    q_pre = np.array([by['prefix'][e]['queue_sum'] for e in eps]); f_pre = np.array([by['prefix'][e]['finished'] for e in eps])
    b_pre = np.array([by['prefix'][e]['bytes'] for e in eps])
    rel_ctl = (q_bid - q_ctl) / q_ctl; rel_pre = (q_bid - q_pre) / q_pre
    out = dict(episodes=len(eps), seeds_bid=mb, seeds_ctl=mc,
               rel_waiting_vs_ctrl=dict(mean=float(rel_ctl.mean()), ci95=boot(rel_ctl), better=int((rel_ctl < 0).sum())),
               rel_waiting_vs_prefix=dict(mean=float(rel_pre.mean()), ci95=boot(rel_pre), better=int((rel_pre < 0).sum())),
               ctrl_rel_waiting_vs_prefix=float(((q_ctl - q_pre) / q_pre).mean()),
               finished_vs_ctrl=float((f_bid - f_ctl).mean()), finished_vs_prefix=float((f_bid - f_pre).mean()),
               bytes_rel_prefix=dict(bid=float(((b_bid - b_pre) / b_pre).mean()), ctrl=float(((b_ctl - b_pre) / b_pre).mean())),
               per_seed_rel_vs_prefix={m: float(np.mean([(by[m][e]['queue_sum'] - by['prefix'][e]['queue_sum']) / by['prefix'][e]['queue_sum'] for e in eps])) for m in mb + mc})
    if 'oracle_heldphase' in by:
        q_or = np.array([by['oracle_heldphase'][e]['queue_sum'] for e in eps])
        out['oracle_rel_waiting_vs_prefix'] = float(((q_or - q_pre) / q_pre).mean())
        out['oracle_finished_vs_prefix'] = float((np.array([by['oracle_heldphase'][e]['finished'] for e in eps]) - f_pre).mean())
    out['c1_ci_upper_vs_ctrl_neg'] = out['rel_waiting_vs_ctrl']['ci95'][1] < 0
    out['c2_mean_vs_prefix_neg'] = out['rel_waiting_vs_prefix']['mean'] < 0
    out['c3_finished_vs_ctrl_nonneg'] = out['finished_vs_ctrl'] >= 0
    out['PASS'] = bool(out['c1_ci_upper_vs_ctrl_neg'] and out['c2_mean_vs_prefix_neg'] and out['c3_finished_vs_ctrl_nonneg'])
    (Path(a.run) / 'verdict.json').write_text(json.dumps(out, indent=1))
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('run'); main(p.parse_args())
