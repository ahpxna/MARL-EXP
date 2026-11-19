#!/usr/bin/env python3
"""Paper figure p9 (13/10/2026): W19 / W20 in the paper style, from research/papers/TSI_two_population/fig3_repr.json (registered W19 / W20
rows; 95 % crossed-bootstrap intervals). A: extra time loss of the fleet's cars against no SPaT, forecast only vs with the repair (TSI on the
RL-H inputs, TSI-G on the library representations), for signals with stop-thresholded inputs, and the forecast alone for signals without
them; both rewards for the W19 families. B: fleet fuel saved as deployed, HBEFA4 and PHEMlight5. Derived from scripts/POSTER_tsi_fig3_bars_v5.py.
Output: research/papers/_tex/figs_two_pop/p9_w19_w20.pdf"""
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

T = Path(__file__).resolve().parents[1] / 'research/papers/TSI_two_population'
D = {e['label']: e for e in json.loads((T / 'fig3_repr.json').read_text())}
THR = [('RL-H (this paper)', 'RL-H\n(ours)'), ('RL-H inputs, delay reward', 'RL-H,\ndelay'), ('sumo-rl default', 'sumo-rl\ndefault'), ('RESCO IDQN / IPPO state', 'RESCO\nIDQN'),
       ('RESCO MPLight state', 'RESCO\nMPLight')]
CTL = [('speed groups', 'speed\ngroups'), ('queue positions', 'queue\npos.'), ('speed groups, delay reward', 'speed,\ndelay'), ('positions, delay reward', 'pos.,\ndelay'), ('RESCO wave state', 'RESCO\nwave')]
THR = [x for x in THR if x[0] in D]; CTL = [x for x in CTL if x[0] in D]
ORANGE, BLUE, LBLUE, LORANGE, GREY = '#E5632D', '#2B6CB0', '#8DB4E2', '#F2A47E', '#555555'
plt.rcParams.update({'font.size': 12, 'axes.titlesize': 13})
fig, (a1, a2) = plt.subplots(1, 2, figsize=(13.5, 4.8), gridspec_kw=dict(width_ratios=[1.4, 1.1], wspace=0.2))
YMAX = 9.8; w = 0.36
x = np.arange(len(THR)); xc = np.arange(len(CTL)) + len(THR) + 0.6


def bar(ax, xx, v, c, lab=None, below=False):
    p, lo, hi = v['point'], v['lo2'], v['hi2']; h = min(p, YMAX)
    ax.bar(xx, h, w, color=c, label=lab, zorder=2)
    ax.errorbar(xx, h, yerr=[[max(0, h - lo)], [max(0, min(hi, YMAX) - h)]], color=GREY, capsize=3, lw=1.2, zorder=3)
    if p > YMAX:                                                      # broken bar: the value is printed
        ax.plot([xx - w / 2, xx + w / 2], [YMAX - 0.35, YMAX - 0.15], color='white', lw=4, zorder=4)
        ax.text(xx, YMAX + 0.1, f'{p:.1f}', ha='center', va='bottom', fontsize=11, color=c, fontweight='bold')
    else:
        t = '0.0' if abs(p) < 0.05 else f'{p:+.1f}'
        if below:                                                     # under the bar, clear of the dashed limit line
            ax.text(xx, min(0.0, lo) - 0.12, t, ha='center', va='top', fontsize=10, color=c)
        else:
            ax.text(xx, max(0.0, min(hi, YMAX)) + 0.15, t, ha='center', va='bottom', fontsize=10, color=c)


for i, (k, _l) in enumerate(THR):
    e = D[k]; bar(a1, x[i] - w / 2, e['sv']['tl'], ORANGE, 'forecast only' if i == 0 else None); bar(a1, x[i] + w / 2, e['fix']['tl'], BLUE, 'with TSI / TSI-G' if i == 0 else None, below=e['fix']['tl']['point'] < 0.25)
for i, (k, _l) in enumerate(CTL):
    bar(a1, xc[i], D[k]['sv']['tl'], ORANGE)
a1.axhline(0, color=GREY, lw=1); a1.set_ylim(-1.75, YMAX + 0.9)
a1.hlines(0.5, x[0] - 0.45, x[-1] + 0.45, color=GREY, lw=1.1, ls='--', zorder=1)   # the registered limit, over the signals that need a repair
a1.set_xticks(list(x) + list(xc)); a1.set_xticklabels([l for _, l in THR] + [l for _, l in CTL], fontsize=9)
a1.set_ylabel("Fleet's extra delay (s/veh)"); a1.set_title("A  The fleet's cars, vs no SPaT", loc='left', fontweight='bold')
a1.axvspan(xc[0] - 0.45, xc[-1] + 0.45, color='#F1F1F1', zorder=0)
a1.text((xc[0] + xc[-1]) / 2, 4.2, 'no stop-thresholded input:\nno repair needed', ha='center', va='center', fontsize=10, style='italic')
for ax_, xs_, lab_ in ((a1, (x[0], x[-1]), 'stop-based inputs'), (a1, (xc[0], xc[-1]), 'control')):
    ax_.annotate(lab_, xy=((xs_[0] + xs_[1]) / 2, 0), xycoords=('data', 'axes fraction'), xytext=(0, -48), textcoords='offset points', ha='center', fontsize=10, style='italic')
a1.spines[['top', 'right']].set_visible(False)
# B: fuel saved as deployed
lab = [l for _, l in THR] + [l for _, l in CTL]; xb = np.arange(len(lab)); xb = np.where(xb >= len(THR), xb + 0.6, xb)
for i, (k, _l) in enumerate(THR + CTL):
    e = D[k]; dep = e['fix'] or e['sv']; c4, c5 = (BLUE, LBLUE) if e['fix'] else (ORANGE, LORANGE)
    for dx, key, c in ((-w / 2, 'f4', c4), (w / 2, 'f5', c5)):
        v = dep[key]; s = -v['point']; a2.bar(xb[i] + dx, s, w, color=c, zorder=2)
        a2.errorbar(xb[i] + dx, s, yerr=[[s + v['hi2']], [-v['lo2'] - s]], color=GREY, capsize=3, lw=1.2, zorder=3)
a2.set_xticks(xb); a2.set_xticklabels([l.replace('\n', ' ') for l in lab], fontsize=8, rotation=45, ha='right', rotation_mode='anchor'); a2.set_ylabel('Fleet fuel saved (%)'); a2.set_title('B  Fuel saved, as deployed', loc='left', fontweight='bold')
a2.axvspan(xb[len(THR)] - 0.45, xb[-1] + 0.45, color='#F1F1F1', zorder=0); a2.set_ylim(0, 11)
from matplotlib.patches import Patch
from matplotlib.lines import Line2D
fig.legend(handles=[Patch(color=ORANGE, label='forecast only'), Patch(color=BLUE, label='with TSI / TSI-G'), Patch(color='#333333', label='B: dark = HBEFA4'),
                    Patch(color='#AAAAAA', label='light = PHEMlight5'), Line2D([], [], color=GREY, ls='--', lw=1.1, label='A: +0.5 limit')], loc='upper center', ncol=5, frameon=False, fontsize=11, bbox_to_anchor=(0.53, 1.02))
a2.spines[['top', 'right']].set_visible(False)
fig.subplots_adjust(left=0.06, right=0.99, top=0.84, bottom=0.24)
O = Path(__file__).resolve().parents[1] / 'research/papers/_tex/figs_two_pop/p9_w19_w20.pdf'; fig.savefig(O); print('saved', O, [k for k, _ in THR + CTL])
