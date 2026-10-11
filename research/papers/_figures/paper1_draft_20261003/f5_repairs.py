"""F5  repairs at the UPGRADED channel: the K1-trained receiver deployed at iid, gain vs Z (%), mean [95 % two-level bootstrap] and seeds.
Frozen-receiver arms (orange): PLAIN / LAB (age relabel) / EMU (receiver-side emulation) from the age-emulation panel 5101-5164;
RELAY / FB_S (support fallback to Z) from the fallback panels (3x3 4801-4864, 4x4 4901-4964).  Replace-the-receiver arms: the
iid-trained receiver (blue) on the same panels, the mixture MIX (violet; 3x3 fallback panel 4801, 4x4 test D 4601) and MIX2 (3x3 4801).
Dashed: the K1-trained receiver on its own channel K = 1 (same panels).  All values recomputed from rows.json (extra_data.json)."""
import json
import numpy as np
from common import *
X = json.loads((OUT / 'extra_data.json').read_text())['cells']; VIOLET = '#4a3aa7'
ARMS = {'4x4': [('4x4|5101|relayCK1_st|iid|PLAIN', 'PLAIN', ORANGE), ('4x4|5101|relayCK1_st|iid|LAB', 'LAB', ORANGE), ('4x4|5101|relayCK1_st|iid|EMU', 'EMU', ORANGE),
                ('4x4|5101|relayCage_st|iid|PLAIN', 'Cage', BLUE), None,
                ('4x4|4901|relayCK1_st|iid|RELAY', 'PLAIN', ORANGE), ('4x4|4901|relayCK1_st|iid|FB_S', 'FB_S', ORANGE), ('4x4|4901|relayCage_st|iid|RELAY', 'Cage', BLUE), None,
                ('4x4|4601|relayCK1_st|iid', 'PLAIN', ORANGE), ('4x4|4601|relayCage_st|iid', 'Cage', BLUE), ('4x4|4601|relayMIX_st|iid', 'MIX', VIOLET)],
        '3x3': [('3x3|5101|relayCK1_st|iid|PLAIN', 'PLAIN', ORANGE), ('3x3|5101|relayCK1_st|iid|LAB', 'LAB', ORANGE), ('3x3|5101|relayCK1_st|iid|EMU', 'EMU', ORANGE),
                ('3x3|5101|relay6Cage_st|iid|PLAIN', '6Cage', BLUE), None,
                ('3x3|4801|relayCK1_st|iid|RELAY', 'PLAIN', ORANGE), ('3x3|4801|relayCK1_st|iid|FB_S', 'FB_S', ORANGE), ('3x3|4801|relay6Cage_st|iid|RELAY', '6Cage', BLUE),
                ('3x3|4801|relayMIX_st|iid|RELAY', 'MIX', VIOLET), ('3x3|4801|relayMIX2_st|iid|RELAY', 'MIX2', VIOLET)]}
OWN = {'4x4': {5101: '4x4|5101|relayCK1_st|K1|PLAIN', 4901: '4x4|4901|relayCK1_st|K1|RELAY', 4601: '4x4|4601|relayCK1_st|K1'},
       '3x3': {5101: '3x3|5101|relayCK1_st|K1|PLAIN', 4801: '3x3|4801|relayCK1_st|K1|RELAY'}}
PANEL_NAME = {5101: 'age-emulation panel 5101', 4901: 'fallback panel 4901', 4801: 'fallback panel 4801', 4601: 'test D panel 4601'}
fig, axes = plt.subplots(1, 2, figsize=(14, 4.9), gridspec_kw=dict(width_ratios=[12, 10], wspace=0.12))
dump = {}
for ax, grid in zip(axes, ('4x4', '3x3')):
    x = 0; groups = []; cur = []
    for a in ARMS[grid]:
        if a is None: groups.append(cur); cur = []; x += 0.6; continue
        k, lab, col = a; c = X[k]; p_ = int(k.split('|')[1])
        ax.bar(x, c['mean'], width=0.7, color=col, alpha=0.85, edgecolor=SURF, linewidth=1.0, zorder=2)
        ax.errorbar(x, c['mean'], yerr=[[c['mean'] - c['lo']], [c['hi'] - c['mean']]], color=INK, lw=1.0, capsize=3, zorder=4)
        v = np.array(c['per_seed']); ax.scatter(x + np.linspace(-0.22, 0.22, len(v)), v, s=9, color=INK2, zorder=3, linewidths=0)
        ax.text(x, -0.02, f"{lab}\n{c['mean']:+.2f}", transform=ax.get_xaxis_transform(), ha='center', va='top', fontsize=7.5, rotation=0)
        cur.append((x, p_)); dump[f'{grid}|{k}'] = dict(label=lab, mean=c['mean'], lo=c['lo'], hi=c['hi'], npos=c['npos'], n=len(v), source=c['source']); x += 1
    groups.append(cur)
    for g in groups:
        x0, x1 = g[0][0] - 0.45, g[-1][0] + 0.45; p_ = g[0][1]; own = X[OWN[grid][p_]]['mean']
        ax.plot([x0, x1], [own, own], color=ORANGE, lw=1.2, ls='--', zorder=5)
        ax.text((x0 + x1) / 2, -0.15, PANEL_NAME[p_] + f'\n(CK1 at K=1: {own:+.2f})', transform=ax.get_xaxis_transform(), ha='center', va='top', fontsize=7.5, color=INK)
    ax.axhline(0, color=INK2, lw=0.8); ax.set_xticks([]); ax.grid(axis='x', visible=False)
    ax.set_title(f'{grid}: the K1-trained receiver deployed at iid, and the alternatives', loc='left', fontsize=9.5)
    if grid == '4x4': ax.set_ylabel('gain vs zero-byte Z at iid (%)')
from matplotlib.patches import Patch
from matplotlib.lines import Line2D
fig.legend(handles=[Patch(color=ORANGE, label='K1-trained receiver (frozen; PLAIN = as deployed, LAB = age relabel, EMU = emulate K=1 views, FB_S = support fallback to Z)'),
                    Patch(color=BLUE, label='replace by the iid-trained receiver'), Patch(color=VIOLET, label='replace by a mixture-trained receiver'), Line2D([], [], color=ORANGE, ls='--', label='K1-trained receiver on its own channel K = 1 (same panel)')],
           loc='upper center', ncol=1, bbox_to_anchor=(0.5, 1.12), fontsize=8)
save(fig, 'F5_repairs_at_upgrade')
json.dump(dump, open(OUT / 'F5_data.json', 'w'), indent=1)
for k, v in dump.items(): print(f'{k:50s} {v["label"]:12s} {v["mean"]:+.2f} [{v["lo"]:+.2f},{v["hi"]:+.2f}] {v["npos"]}/{v["n"]}')
