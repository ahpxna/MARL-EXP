"""F1  train x deploy heatmaps (gain vs the same-seed zero-byte student Z, %; pooled over finished K-grid panels).
Cell: mean [95 % seed-bootstrap CI], seeds > 0 / n.  Outlined cells = deployment channel is (one of) the receiver's training
channel(s).  Sources: pooled_data.py (3x3 = e3_train_deploy_matrix_20261003/matrix.json exactly; 4x4 = matrix.json + test D 4601)."""
import json
import numpy as np
from matplotlib.colors import TwoSlopeNorm
from matplotlib.patches import Rectangle
from common import *
from pooled_data import pooled, ORDER
P = pooled(True)
ROWS = {'3x3': [('relay6Cage_st', 'iid-trained (6Cage)', {'iid'}), ('relayCK1_st', 'K1-trained (CK1)', {'K1'}), ('relayCK2_st', 'K2-trained (CK2)', {'K2'}),
                ('relayMIX_st', 'mixture K1-K3+iid (MIX)', set(ORDER)), ('relayMIX2_st', 'mixture K1+iid (MIX2)', {'K1', 'iid'})],
        '4x4': [('relayCage_st', 'iid-trained (Cage)', {'iid'}), ('relayCK1_st', 'K1-trained (CK1)', {'K1'}), ('relayMIX_st', 'mixture K1-K3+iid (MIX)', set(ORDER))]}
COLS = ['K1', 'K2', 'K3', 'iid']; COLLAB = ['K = 1', 'K = 2', 'K = 3', 'iid K']
def lum(rgb):
    r, g, b = rgb[:3]; return 0.2126 * r + 0.7152 * g + 0.0722 * b
fig, axes = plt.subplots(1, 2, figsize=(13.5, 4.6), gridspec_kw=dict(width_ratios=[1, 1], wspace=0.55))
dump = {}
for ax, grid in zip(axes, ('3x3', '4x4')):
    rows = ROWS[grid]; M = np.full((len(rows), 4), np.nan)
    for i, (fam, _, _) in enumerate(rows):
        for j, K in enumerate(COLS):
            if (grid, fam, K) in P: M[i, j] = P[(grid, fam, K)]['mean']
    vmax = np.nanmax(np.abs(M)) * 1.05; norm = TwoSlopeNorm(0, -vmax, vmax)
    im = ax.imshow(M, cmap=DIVERGING, norm=norm, aspect='auto')
    ax.grid(False); ax.set_xticks(range(4), COLLAB); ax.set_yticks(range(len(rows)), [r[1] for r in rows])
    ax.tick_params(length=0); [s.set_visible(False) for s in ax.spines.values()]
    for i, (fam, _, diag) in enumerate(rows):
        for j, K in enumerate(COLS):
            c = P.get((grid, fam, K))
            if c is None: continue
            col = 'white' if lum(DIVERGING(norm(c['mean']))) < 0.45 else INK
            ax.text(j, i - 0.2, f"{c['mean']:+.2f}", ha='center', va='center', fontsize=10, fontweight='bold', color=col)
            ax.text(j, i + 0.1, f"[{c['lo']:+.1f}, {c['hi']:+.1f}]", ha='center', va='center', fontsize=6.5, color=col)
            ax.text(j, i + 0.32, f"{c['npos']}/{len(c['seeds'])} seeds > 0", ha='center', va='center', fontsize=6, color=col)
            if K in diag:
                ax.add_patch(Rectangle((j - 0.48, i - 0.48), 0.96, 0.96, fill=False, ec=INK, lw=1.8))
            dump[f'{grid}|{fam}|{K}'] = dict(mean=c['mean'], lo=c['lo'], hi=c['hi'], npos=c['npos'], n=len(c['seeds']), panels=c['panels'], diagonal=K in diag)
    cb = fig.colorbar(im, ax=ax, fraction=0.04, pad=0.02); cb.set_label('gain vs zero-byte Z (%)', color=INK2); cb.outline.set_visible(False)
    ax.set_title(f"{grid} grid — deployment channel →", loc='left', fontsize=10, color=INK)
    ax.set_xlabel('deployment channel (quality K = 1 < 2 < 3 < iid)')
fig.text(0.01, -0.06, 'Outlined: deployment = a training channel.  Cell: mean over seeds of the per-seed gain averaged over all finished panels containing the cell '
         '[95 % seed bootstrap], seeds > 0 / n.\n3x3 panels: 2801–4501 (13); 4x4: 2901, 3301, 4201, 4301, 4601.  Single-panel rows: 3x3 CK2 (3901), MIX2 (4501); 4x4 MIX (4601).',
         fontsize=7, color=INK2)
save(fig, 'F1_train_deploy_heatmaps')
json.dump(dump, open(OUT / 'F1_data.json', 'w'), indent=1)
print('F1 written')
