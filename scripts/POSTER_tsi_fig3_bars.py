#!/usr/bin/env python3
"""Poster Fig. 3, bar version (09/10/2026), from research/papers/TSI_two_population/fig3_repr.json (written by POSTER_tsi_fig3_repr.py from the
registered W19 / W20 rows; 95 % crossed-bootstrap intervals).  A: extra time loss of the fleet's cars against no SPaT, forecast only vs with
the repair, for the signals that count stopped cars, and the forecast alone for signals that see speed or position.  B: fleet fuel saved as
deployed (repair where needed), HBEFA4 and PHEMlight5.  Output: research/papers/TSI_two_population/fig3_bars.png"""
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

T = Path(__file__).resolve().parents[1] / 'research/papers/TSI_two_population'
D = {e['label']: e for e in json.loads((T / 'fig3_repr.json').read_text())}
THR = [('RL-H (this paper)', 'RL-H\n(ours)'), ('sumo-rl default', 'sumo-rl\ndefault'), ('RESCO IDQN / IPPO state', 'RESCO\nIDQN'),
       ('RESCO MPLight state', 'RESCO\nMPLight')]
CTL = [('speed groups', 'speed\ngroups'), ('queue positions', 'queue\npositions'), ('RESCO wave state', 'RESCO\nwave')]
THR = [x for x in THR if x[0] in D]; CTL = [x for x in CTL if x[0] in D]
ORANGE, BLUE, LBLUE, LORANGE, GREY = '#E5632D', '#2B6CB0', '#8DB4E2', '#F2A47E', '#555555'
plt.rcParams.update({'font.family': 'Times New Roman', 'font.size': 17, 'axes.titlesize': 19})
fig, (a1, a2) = plt.subplots(1, 2, figsize=(12.6, 5.6), gridspec_kw=dict(width_ratios=[1.4, 1.1], wspace=0.2))
YMAX = 9.8; w = 0.36
x = np.arange(len(THR)); xc = np.arange(len(CTL)) + len(THR) + 0.6


def bar(ax, xx, v, c, lab=None):
    p, lo, hi = v['point'], v['lo2'], v['hi2']; h = min(p, YMAX)
    ax.bar(xx, h, w, color=c, label=lab, zorder=2)
    ax.errorbar(xx, h, yerr=[[max(0, h - lo)], [max(0, min(hi, YMAX) - h)]], color=GREY, capsize=3, lw=1.2, zorder=3)
    if p > YMAX:                                                      # broken bar: the value is printed
        ax.plot([xx - w / 2, xx + w / 2], [YMAX - 0.35, YMAX - 0.15], color='white', lw=4, zorder=4)
        ax.text(xx, YMAX + 0.1, f'{p:.1f}', ha='center', va='bottom', fontsize=15, color=c, fontweight='bold')
    else:
        t = '0.0' if abs(p) < 0.05 else f'{p:+.1f}'; ax.text(xx, max(0.0, min(hi, YMAX)) + 0.15, t, ha='center', va='bottom', fontsize=14, color=c)


for i, (k, _l) in enumerate(THR):
    e = D[k]; bar(a1, x[i] - w / 2, e['sv']['tl'], ORANGE, 'forecast only' if i == 0 else None); bar(a1, x[i] + w / 2, e['fix']['tl'], BLUE, 'with TSI / TSI-G' if i == 0 else None)
for i, (k, _l) in enumerate(CTL):
    bar(a1, xc[i], D[k]['sv']['tl'], ORANGE)
a1.axhline(0, color=GREY, lw=1); a1.set_ylim(-1.6, YMAX + 0.9)
a1.set_xticks(list(x) + list(xc)); a1.set_xticklabels([l for _, l in THR] + [l for _, l in CTL], fontsize=14)
a1.set_ylabel("Fleet's extra wait (s/veh)"); a1.set_title("A  The fleet's cars, vs no SPaT", loc='left', fontweight='bold')
a1.axvspan(xc[0] - 0.45, xc[-1] + 0.45, color='#F1F1F1', zorder=0)
a1.text((xc[0] + xc[-1]) / 2, 4.2, 'sees speed\nor position:\nno repair\nneeded', ha='center', va='center', fontsize=14, style='italic')
for ax_, xs_, lab_ in ((a1, (x[0], x[-1]), 'counts only stopped cars'), (a1, (xc[0], xc[-1]), 'control')):
    ax_.annotate(lab_, xy=((xs_[0] + xs_[1]) / 2, 0), xycoords=('data', 'axes fraction'), xytext=(0, -62), textcoords='offset points', ha='center', fontsize=14, style='italic')
a1.spines[['top', 'right']].set_visible(False)
# B: fuel saved as deployed
lab = [l for _, l in THR] + [l for _, l in CTL]; xb = np.arange(len(lab)); xb = np.where(xb >= len(THR), xb + 0.6, xb)
for i, (k, _l) in enumerate(THR + CTL):
    e = D[k]; dep = e['fix'] or e['sv']; c4, c5 = (BLUE, LBLUE) if e['fix'] else (ORANGE, LORANGE)
    for dx, key, c in ((-w / 2, 'f4', c4), (w / 2, 'f5', c5)):
        v = dep[key]; s = -v['point']; a2.bar(xb[i] + dx, s, w, color=c, zorder=2)
        a2.errorbar(xb[i] + dx, s, yerr=[[s + v['hi2']], [-v['lo2'] - s]], color=GREY, capsize=3, lw=1.2, zorder=3)
a2.set_xticks(xb); a2.set_xticklabels([l.replace('queue\npositions', 'queue\npos.').replace('sumo-rl\ndefault', 'sumo-rl\ndef.').replace('RESCO\nMPLight', 'RESCO\nMPL.').replace('speed\ngroups', 'speed\ngr.') for l in lab], fontsize=12); a2.set_ylabel('Fleet fuel saved (%)'); a2.set_title('B  Fuel saved, as deployed', loc='left', fontweight='bold')
a2.axvspan(xb[len(THR)] - 0.45, xb[-1] + 0.45, color='#F1F1F1', zorder=0); a2.set_ylim(0, 11)
from matplotlib.patches import Patch
fig.legend(handles=[Patch(color=ORANGE, label='forecast only'), Patch(color=BLUE, label='with TSI / TSI-G'), Patch(color='#333333', label='B: dark = HBEFA4'),
                    Patch(color='#AAAAAA', label='light = PHEMlight5')], loc='upper center', ncol=4, frameon=False, fontsize=15, bbox_to_anchor=(0.53, 1.0))
a2.spines[['top', 'right']].set_visible(False)
fig.subplots_adjust(left=0.07, right=0.99, top=0.84, bottom=0.2)
fig.savefig(T / 'fig3_bars.png', dpi=300); print('saved', T / 'fig3_bars.png', [k for k, _ in THR + CTL])
