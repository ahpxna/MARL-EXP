#!/usr/bin/env python3
"""Figures for the TSI result (05/10): reads the registered reports through the dashboard's generic contrast parser (scripts/DASH_build.py).
fig3_tsi_components: TSI-2 / HYB / ADP2 / F1-B vs R on the confirmation panel (C-118), four endpoints, 95 % CI.
fig4_tsi_mechanism:  (a) per-light residual green lengthening vs agent time cost (C-114 rows, TSI and HYB); (b) X3 / N2 open vs closed loop.
fig5_tsi_scope:      TSI-2 vs R across receiver classes, penetration and the demand shift (C-120, C-121), agent fuel and agent TL."""
import importlib.util, json, sys
from pathlib import Path
import numpy as np
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT)); CS = ROOT / 'research/city_sim'; OUT = ROOT / 'research/papers/_tex/figs_two_pop'
spec = importlib.util.spec_from_file_location('D', ROOT / 'scripts/DASH_build.py'); D = importlib.util.module_from_spec(spec); spec.loader.exec_module(D)
from scripts.CITY_spatp_report import rows  # noqa: E402
rowsof = lambda p: {r['name']: r['m'] for r in D.ch_contrasts((CS / p).read_text())['rows']}
MET = (('fuel', 'agent fuel (%)'), ('agentTL', 'agent TL (s/veh)'), ('cityTL', 'city TL (s/veh)'), ('humanTL', 'human TL (s/veh)'))


def bars(ax, names, R, key, title, colors):
    v = [R[n][key]['v'] for n in names]; lo = [R[n][key]['v'] - R[n][key]['lo'] for n in names]; hi = [R[n][key]['hi'] - R[n][key]['v'] for n in names]
    ax.bar(range(len(names)), v, yerr=[lo, hi], color=colors, capsize=3); ax.axhline(0, color='k', lw=0.8); ax.set_xticks(range(len(names)))
    ax.set_xticklabels([n.split(' - ')[0].replace('(a) ', '').replace('(c) ', '') for n in names], rotation=25, ha='right', fontsize=8); ax.set_title(title, fontsize=9)
    if key != 'fuel':
        ax.axhline(0.5, color='r', ls='--', lw=0.8)


if __name__ == '__main__':
    R = rowsof('tsi2_20261005/report_tsi2_confirm.txt'); names = ['TSI2 - R', 'HYB - R', 'ADP2 - R', 'F1B - R']; col = ['#1f77b4', '#ff7f0e', '#7f7f7f', '#2ca02c']
    fig, axs = plt.subplots(1, 4, figsize=(12, 3.2))
    for ax, (k, t) in zip(axs, MET):
        bars(ax, names, R, k, t, col)
    fig.suptitle('TSI-2 confirmation vs R (lights t4-t8 x fleets s213-s513 x traffic 720-739; 95% CI; dashed = +0.5 s/veh margin)', fontsize=9); fig.tight_layout()
    fig.savefig(OUT / 'fig3_tsi_components.pdf'); fig.savefig(OUT / 'fig3_tsi_components.png', dpi=150)
    Rt = rows(CS / 'tsi_20261005/conf'); FL = ('s213', 's313', 's413', 's513'); S = range(700, 720)
    m = lambda a, t, q: np.mean([Rt[f'{a}_t{t}_{f}'][s][q] for f in FL for s in S])
    fig, axs = plt.subplots(1, 2, figsize=(9, 3.4))
    for a, c in (('TSI', '#1f77b4'), ('HYB', '#ff7f0e')):
        x = [m(a, t, 'green_mean') - m('R', t, 'green_mean') for t in (4, 5, 6, 7, 8)]; y = [m(a, t, 'timeloss_agent') - m('R', t, 'timeloss_agent') for t in (4, 5, 6, 7, 8)]
        axs[0].scatter(x, y, color=c, label=a)
        for t, xi, yi in zip((4, 5, 6, 7, 8), x, y):
            axs[0].annotate(f't{t}', (xi, yi), fontsize=7)
    axs[0].axhline(0.5, color='r', ls='--', lw=0.8); axs[0].set_xlabel('mean green lengthening vs R (s)'); axs[0].set_ylabel('agent TL vs R (s/veh)'); axs[0].legend(fontsize=8)
    axs[0].set_title('(a) hidden demand: longer greens cost the eco fleet time', fontsize=9)
    X = rowsof('n2m_20261005/report_x3.txt'); N = rowsof('n2m_20261005/report_n2m.txt')
    lab = ['exact (open loop)', 'N2 (open loop)', 'N2 (closed loop)']; F = [X['RPex - RPsig']['fuel']['v'], X['RPn2 - RPsig']['fuel']['v'], N['N2q05 - R']['fuel']['v']]
    A = [X['RPex - RPsig']['agentTL']['v'], X['RPn2 - RPsig']['agentTL']['v'], N['N2q05 - R']['agentTL']['v']]
    axs[1].scatter(A, F, color=['#2ca02c', '#ff7f0e', '#d62728'])
    for l, a, f in zip(lab, A, F):
        axs[1].annotate(l, (a, f), fontsize=7)
    axs[1].axhline(0, color='k', lw=0.6); axs[1].axvline(0.5, color='r', ls='--', lw=0.8); axs[1].set_xlabel('agent TL (s/veh)'); axs[1].set_ylabel('agent fuel (%)')
    axs[1].set_title('(b) exact timing costs no time; forecast errors do', fontsize=9); fig.tight_layout()
    fig.savefig(OUT / 'fig4_tsi_mechanism.pdf'); fig.savefig(OUT / 'fig4_tsi_mechanism.png', dpi=150)
    G = rowsof('gen_20261005/report_gen.txt'); Sh = rowsof('shift_20261005/report_shift.txt')
    items = [('PPO R10 (conf.)', R['TSI2 - R']), ('PPO R10 (750-759)', G['(b) TSI2 - R']), ('rule R8', G['(a) rule TSI2 - R']), ('search R9', G['(a) r9 TSI2 - R']),
             ('share 25%', G['(c) rho 0.25 TSI2 - R']), ('share 75%', G['(c) rho 0.75 TSI2 - R']), ('demand +25%', Sh['TSI2 - R'])]
    fig, axs = plt.subplots(1, 2, figsize=(10, 3.4))
    for ax, k, t in ((axs[0], 'fuel', 'agent fuel vs R (%)'), (axs[1], 'agentTL', 'agent TL vs R (s/veh)')):
        v = [it[1][k]['v'] for it in items]; e = [[it[1][k]['v'] - it[1][k]['lo'] for it in items], [it[1][k]['hi'] - it[1][k]['v'] for it in items]]
        ax.bar(range(len(items)), v, yerr=e, capsize=3, color='#1f77b4'); ax.axhline(0, color='k', lw=0.8); ax.set_xticks(range(len(items)))
        ax.set_xticklabels([it[0] for it in items], rotation=25, ha='right', fontsize=8); ax.set_title(t, fontsize=9)
        if k == 'agentTL':
            ax.axhline(0.5, color='r', ls='--', lw=0.8)
    fig.suptitle('Scope of TSI-2 (design frozen): receiver classes, fleet share, demand shift (95% CI)', fontsize=9); fig.tight_layout()
    fig.savefig(OUT / 'fig5_tsi_scope.pdf'); fig.savefig(OUT / 'fig5_tsi_scope.png', dpi=150); print('ok')
