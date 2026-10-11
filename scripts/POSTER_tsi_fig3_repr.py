#!/usr/bin/env python3
"""Poster Fig. 3 (09/10/2026): the fleet's time loss and fuel against no SPaT, by signal representation, from the registered W19 / W20 rows
(fresh traffic 1400-1419, 5 lights x 4 frozen fleets x 20 seeds, crossed bootstrap 95 % intervals via CITY_w6_report_v2.paired).
Rows: forecast only (SV - R) and, where the signal counts stopped cars, the repair (TSI adapter for halting counts: TG - R; TSI-G for the
benchmark representations: BIS - R).  Families whose rows are not complete are left out and listed on stdout.
Output: research/papers/TSI_two_population/fig3_repr.png (+ .json with the plotted numbers)."""
import json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import scripts.CITY_w6_report_v2 as V
from scripts.CITY_w6_validation import rows

FS = ('s1413', 's1513', 's1613', 's1713'); S = list(range(1400, 1420)); K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
D19, D20 = ROOT / 'research/city_sim/w19_20261008/conf', ROOT / 'research/city_sim/w20_20261009/conf'
OUT = ROOT / 'research/papers/TSI_two_population/fig3_repr.png'
# (label, group, light k0, rows dir, repair arm or None)
FAM = [('RL-H (this paper)', 0, 34, D19, 'TG'), ('RL-H inputs, delay reward', 0, 49, D19, 'TG'), ('sumo-rl default', 0, 84, D20, 'BIS'),
       ('RESCO IDQN / IPPO state', 0, 89, D20, 'BIS'), ('RESCO MPLight state', 0, 94, D20, 'BIS'),
       ('speed groups', 1, 39, D19, None), ('queue positions', 1, 44, D19, None), ('speed groups, delay reward', 1, 54, D19, None),
       ('positions, delay reward', 1, 59, D19, None), ('RESCO wave state', 1, 99, D20, None)]
R = {D19: rows(D19), D20: rows(D20)}
R[D20].update({k: v for k, v in R[D19].items() if k.split('_t')[1].startswith(('34_', '35_', '36_', '37_', '38_'))})


def have(Rt, a, k0):
    return all(f'{a}{x}_t{k}_{f}' in Rt and set(Rt[f'{a}{x}_t{k}_{f}']) >= set(S) for k in range(k0, k0 + 5) for f in FS for x in ('', 'P5'))


def cmp(Rt, a, k0):
    L = tuple(range(k0, k0 + 5)); r = V.paired(Rt, K(a), K('R'), L, FS, S); r5 = V.paired(Rt, K(a + 'P5'), K('RP5'), L, FS, S)
    return dict(tl=r['timeloss_agent'], f4=r['fuel_agent'], f5=r5['fuel_agent'])


data = []
for lab, g, k0, d, fix in FAM:
    Rt = R[d]
    if not (have(Rt, 'R', k0) and have(Rt, 'SV', k0) and (fix is None or have(Rt, fix, k0))):
        print('incomplete, left out:', lab); continue
    e = dict(label=lab, group=g, sv=cmp(Rt, 'SV', k0)); e['fix'] = cmp(Rt, fix, k0) if fix else None; e['fix_name'] = {'TG': 'TSI', 'BIS': 'TSI-G'}.get(fix)
    data.append(e)
OUT.with_suffix('.json').write_text(json.dumps(data, indent=1, default=float))

ORANGE, BLUE, GREY = '#E5632D', '#2B6CB0', '#8A8A8A'
plt.rcParams.update({'font.family': 'Times New Roman', 'font.size': 17, 'axes.titlesize': 18, 'axes.labelsize': 17})
fig, (a1, a2) = plt.subplots(1, 2, figsize=(12.6, 6.0), sharey=True, gridspec_kw=dict(width_ratios=[1.35, 1], wspace=0.06))
ys = []; y = 0.0; ticks = []; heads = []
for gi, gname in ((0, 'Counts only stopped cars'), (1, 'Sees speed or position')):
    heads.append((y, gname)); y += 0.85
    for e in [e for e in data if e['group'] == gi]:
        ys.append((y, e)); ticks.append((y, e['label'])); y += 1.0
    y += 0.35
for yy, e in ys:
    s = e['sv']['tl']; XM = 10.0
    a1.plot([s['lo2'], min(s['hi2'], XM)], [yy - 0.16, yy - 0.16], color=ORANGE, lw=2.4)
    if s['point'] <= XM:
        a1.plot(s['point'], yy - 0.16, 'o', color=ORANGE, ms=8)
    if s['hi2'] > XM:                                                  # off scale: arrow at the edge, the numbers printed
        a1.plot(XM, yy - 0.16, '>', color=ORANGE, ms=10)
        if s['point'] > XM:
            a1.text(XM - 0.2, yy - 0.5, f"{s['point']:+.1f} [{s['lo2']:.1f}, {s['hi2']:.1f}]", ha='right', va='center', fontsize=13, color=ORANGE)
    if e['fix']:
        f = e['fix']['tl']; a1.plot([f['lo2'], f['hi2']], [yy + 0.16, yy + 0.16], color=BLUE, lw=2.4); a1.plot(f['point'], yy + 0.16, 's', color=BLUE, ms=8)
    dep = e['fix'] or e['sv']; c = BLUE if e['fix'] else ORANGE
    for key, mk, dy in (('f4', 'o', -0.12), ('f5', 'o', 0.14)):
        q = dep[key]; a2.plot([q['lo2'], q['hi2']], [yy + dy, yy + dy], color=c, lw=2.2)
        a2.plot(q['point'], yy + dy, mk, color=c, ms=8, mfc=c if key == 'f4' else 'white', mew=2)
for ax in (a1, a2):
    ax.axvline(0, color=GREY, lw=1.2)
    for yh, gname in heads:
        ax.axhspan(yh - 0.45, yh + 0.38, color='#EFEFEF', zorder=0)
    ax.spines[['top', 'right']].set_visible(False); ax.tick_params(axis='y', length=0)
a1.axvline(0.5, color='black', lw=1.2, ls='--'); a1.text(0.6, -0.95, '+0.5 s/veh limit', fontsize=13)
for yh, gname in heads:
    a1.text(-0.015, yh, gname, fontsize=16, fontweight='bold', va='center', ha='right', transform=a1.get_yaxis_transform())
a1.set_yticks([t for t, _ in ticks]); a1.set_yticklabels([l for _, l in ticks]); a1.set_ylim(y - 0.2, -1.3)
a1.set_xlim(-1.5, 10.4); a1.set_xlabel('Fleet time loss vs no SPaT (s/veh)')
a1.set_title('A  Who pays: the fleet\'s cars', loc='left', fontweight='bold')
a2.set_xlabel('Fleet fuel vs no SPaT (%)'); a2.set_title('B  Fuel, as deployed', loc='left', fontweight='bold')
from matplotlib.lines import Line2D
h = [Line2D([], [], color=ORANGE, marker='o', lw=2.4, ms=8, label='forecast only'), Line2D([], [], color=BLUE, marker='s', lw=2.4, ms=8, label='with the repair (TSI / TSI-G)'),
     Line2D([], [], color='black', marker='o', lw=0, ms=8, label='HBEFA4'), Line2D([], [], color='black', marker='o', lw=0, ms=8, mfc='white', mew=2, label='PHEMlight5')]
fig.legend(handles=h, loc='lower center', ncol=4, frameon=False, fontsize=15, bbox_to_anchor=(0.56, -0.005))
fig.subplots_adjust(left=0.23, right=0.99, top=0.92, bottom=0.2)
fig.savefig(OUT, dpi=300); print('saved', OUT, 'rows', [e['label'] for e in data])
