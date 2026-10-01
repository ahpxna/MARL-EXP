#!/usr/bin/env python3
"""Read MARL_e3_label_horizon_probe.py outputs (read-only): does the 3-step label g3 predict the full-episode gain
g_full of a single edit followed by the prefix?  Per actor: the stored oracle-best candidate (chosen by g3) and the
random feasible candidates: mean g3, g_full, g_rest = g_full - g3, P(g_full > 0), P(g_full < 0), and g_full as a % of
the prefix episode queue sum (the closed-loop metric); within-state Spearman(g3, g_full); regret on g_full of choosing
by g3.  Traffic-seed cluster bootstrap (both headways of a seed together).  Refuses an incomplete probe directory.
Usage: MARL_e3_label_horizon_report.py DIR... --out X.json
"""
from __future__ import annotations
import argparse, json, re, sys
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_panel_report import boot_cluster


def main(a):
    out = {}; lines = []; pooled = []
    for D in map(Path, a.dirs):
        man = json.loads((D / 'manifest.json').read_text())
        if man.get('status') != 'COMPLETE' or man.get('self_check') != 'PASS':
            raise SystemExit(f'refusing: {D} not COMPLETE/PASS')
        H = man['H']; R = json.loads((D / 'rows.json').read_text()); per = []
        for r in R:
            Q = np.array(r['queues']); g3 = -(Q[:, :H].sum(1) - Q[0, :H].sum()); gf = -(Q.sum(1) - Q[0].sum()); P = r['prefix_episode_queue_sum']
            rnd = np.arange(2, len(g3))
            rho = spearmanr(g3, gf).correlation if np.ptp(g3) > 0 and np.ptp(gf) > 0 else np.nan
            per.append(dict(seed=int(re.match(r'seed(\d+)_', r['episode']).group(1)), best_g3=g3[1], best_gf=gf[1], best_gf_pct=100 * gf[1] / P,
                            rnd_g3=g3[rnd].mean(), rnd_gf=gf[rnd].mean(), rnd_gf_pct=100 * gf[rnd].mean() / P, rnd_neg=np.mean(gf[rnd] < 0),
                            rnd_g3_neg=np.mean(g3[rnd] < 0), best_pos=float(gf[1] > 0), best_neg=float(gf[1] < 0), rho=rho,
                            regret=gf.max() - gf[int(np.argmax(g3))], max_gf=gf.max()))
        pooled += per
        res = {}
        for k in per[0]:
            if k == 'seed':
                continue
            v = np.array([p[k] for p in per], float); cl = {}
            for p, x in zip(per, v):
                cl.setdefault(p['seed'], []).append(x)
            res[k] = dict(mean=float(np.nanmean(v)), ci=boot_cluster({s: np.array(x) for s, x in cl.items()}))
        out[str(D)] = dict(states=len(per), **res)
        f = lambda k: f"{res[k]['mean']:+.2f} [{res[k]['ci'][0]:+.2f},{res[k]['ci'][1]:+.2f}]"
        lines.append(f"{D.name}: n {len(per)} | stored best g3 {f('best_g3')} g_full {f('best_gf')} ({f('best_gf_pct')}% of prefix episode) "
                     f"P(g_full>0) {res['best_pos']['mean']:.2f} P(<0) {res['best_neg']['mean']:.2f} | random feasible g3 {f('rnd_g3')} g_full {f('rnd_gf')} "
                     f"({f('rnd_gf_pct')}%) P(g_full<0) {res['rnd_neg']['mean']:.2f} P(g3<0) {res['rnd_g3_neg']['mean']:.2f} | "
                     f"Spearman(g3,g_full) {res['rho']['mean']:.2f} | regret of g3-choice on g_full {f('regret')} (max g_full {f('max_gf')})")
    Path(a.out).write_text(json.dumps(out, indent=1)); print('\n'.join(lines), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('dirs', nargs='+'); p.add_argument('--out', required=True)
    main(p.parse_args())
