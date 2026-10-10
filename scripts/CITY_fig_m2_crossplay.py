#!/usr/bin/env python3
"""Figure 1 of paper_two_population: the frozen fleet's benefit against σ* (agent fuel %, and agent time loss) under the old light (FT) and the
upgraded learned light (labelled = publishes no SPaT; naive = the fleet keeps deriving SPaT from the static program).  Raw rows, crossed bootstrap
(CITY_m2_report.cube / fm): grid4 M2a (fresh 470-489; F0a = R9, F0b = R10; four light seeds paired with four fleet seeds) and spider stage 3
(fresh 1000-1019; the rule; two light seeds)."""
import sys
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt  # noqa: E402
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
import scripts.CITY_m2_report as M2  # noqa: E402
OUT = ROOT / 'research/papers/_tex/figs_two_pop'


def grid4():
    Rt = rows(ROOT / 'research/city_sim/spat_pilot_20261004/m2/eval'); M2.S = list(range(470, 490)); K = (0, 1, 2, 3); dr = R.draws((4, 20)); out = {}
    for fl, seeds in (('R9 (grid4)', [f's{k + 2}' for k in K]), ('R10 (grid4)', [f's{213 + 100 * k}' for k in K])):
        tag = 'F0a' if fl.startswith('R9') else 'F0b'; sL0 = [Rt['S03_FT']] * 4; sL1 = [Rt[f'S03_RLH{k}'] for k in K]
        out[fl] = {'old light (FT)': [M2.fm(M2.cube([Rt[f'{tag}_FT_{s}'] for s in seeds], sL0, key, pct), dr) for key, pct in (('fuel_agent', True), ('timeloss_agent', False))]}
        for arm in ('labelled', 'naive'):
            out[fl][f'learned light, {arm}'] = [M2.fm(M2.cube([Rt[f'{tag}_RLH{k}_{arm}'] for k in K], sL1, key, pct), dr) for key, pct in (('fuel_agent', True), ('timeloss_agent', False))]
    return out


def spider():
    Rt = rows(ROOT / 'research/city_sim/m4_20261004/spider/s3/eval'); M2.S = list(range(1000, 1020)); K = (11, 111); dr = R.draws((2, 20))
    sL0 = [Rt['S03_FT']] * 2; sL1 = [Rt[f'S03_RLK{k}'] for k in K]
    o = {'old light (FT)': [M2.fm(M2.cube([Rt['F0_FT']] * 2, sL0, key, pct), dr) for key, pct in (('fuel_agent', True), ('timeloss_agent', False))]}
    for arm in ('labelled', 'naive'):
        o[f'learned light, {arm}'] = [M2.fm(M2.cube([Rt[f'F0_RLK{k}_{arm}'] for k in K], sL1, key, pct), dr) for key, pct in (('fuel_agent', True), ('timeloss_agent', False))]
    return {'rule (spider)': o}


if __name__ == '__main__':
    D = {**grid4(), **spider()}; conds = ['old light (FT)', 'learned light, labelled', 'learned light, naive']; cols = ('tab:green', 'tab:gray', 'tab:red')
    fig, ax = plt.subplots(1, 2, figsize=(11, 3.8)); xs = np.arange(len(D)); w = 0.26
    for j, (ylab, idx) in enumerate((('agent fuel %, fleet vs σ* under the same light', 0), ('agent time loss, s/veh, fleet vs σ*', 1))):
        a = ax[j]
        for i, (c, col) in enumerate(zip(conds, cols)):
            v = [D[f][c][idx] for f in D]; p = [x[0] for x in v]; lo = [x[0] - x[1][0] for x in v]; hi = [x[1][1] - x[0] for x in v]
            a.bar(xs + (i - 1) * w, p, w, yerr=[lo, hi], color=col, capsize=2, label=c)
        a.axhline(0, color='k', lw=0.6); a.set_xticks(xs); a.set_xticklabels(list(D), fontsize=8); a.set_ylabel(ylab, fontsize=8)
        if idx == 1:
            a.axhline(0.5, color='0.4', ls=':', lw=0.8)
    ax[0].legend(fontsize=7); ax[0].set_title('A. fuel benefit (negative = the fleet saves fuel)', fontsize=9); ax[1].set_title('B. agent time loss (dotted: +0.5 margin)', fontsize=9)
    fig.tight_layout(); OUT.mkdir(parents=True, exist_ok=True)
    for ext in ('pdf', 'png'):
        fig.savefig(OUT / f'fig1_m2_crossplay.{ext}', dpi=160)
    for f in D:
        print(f, {c: (round(D[f][c][0][0], 2), round(D[f][c][1][0], 2)) for c in conds})
