"""F4  gain vs channel quality (K = 1 < 2 < 3 < iid) per receiver type: thin lines = seeds (per-seed gain averaged over the finished
panels containing each cell, as F1), bold = mean with 95 % seed-bootstrap band; shaded column(s) = training channel(s); dashed 0 =
the same-seed zero-byte student Z.  Sources: pooled_data.py (3x3 = matrix.json; 4x4 = matrix.json + test D 4601)."""
import json
import numpy as np
from common import *
from pooled_data import pooled, ORDER
P = pooled(True)
VIOLET = '#4a3aa7'
ROWS = [('3x3', [('relay6Cage_st', 'iid-trained (6Cage)', {'iid'}, BLUE), ('relayCK1_st', 'K1-trained (CK1)', {'K1'}, ORANGE), ('relayCK2_st', 'K2-trained (CK2)', {'K2'}, AQUA),
                 ('relayMIX_st', 'mixture: K1,K2,K3,iid (MIX)', set(ORDER), VIOLET), ('relayMIX2_st', 'mixture: K1 + iid (MIX2)', {'K1', 'iid'}, VIOLET)]),
        ('4x4', [('relayCage_st', 'iid-trained (Cage)', {'iid'}, BLUE), ('relayCK1_st', 'K1-trained (CK1)', {'K1'}, ORANGE), ('relayMIX_st', 'mixture: K1,K2,K3,iid (MIX)', set(ORDER), VIOLET)])]
fig, axes = plt.subplots(2, 5, figsize=(15, 6.6), gridspec_kw=dict(hspace=0.55, wspace=0.12))
dump = {}
for r, (grid, recs) in enumerate(ROWS):
    yl = (-6, 7) if grid == '3x3' else (-14, 14)
    for c in range(5):
        ax = axes[r, c]
        if c >= len(recs): ax.set_visible(False); continue
        fam, name, diag, col = recs[c]
        cells = [P[(grid, fam, K)] for K in ORDER]; S = sorted(set.intersection(*[set(x['seeds']) for x in cells]))
        Y = np.array([[dict(zip(x['seeds'], x['per_seed']))[s] for x in cells] for s in S])
        for k, K in enumerate(ORDER):
            if K in diag: ax.axvspan(k - 0.4, k + 0.4, color=GRID, alpha=0.9, zorder=0, lw=0)
        for y in Y: ax.plot(range(4), y, color=col, alpha=0.3, lw=0.9, zorder=2)
        m = Y.mean(0); lo = [x['lo'] for x in cells]; hi = [x['hi'] for x in cells]
        ax.fill_between(range(4), lo, hi, color=col, alpha=0.12, lw=0, zorder=1)
        ax.plot(range(4), m, color=col, lw=2.2, marker='o', ms=6, zorder=4, markeredgecolor=SURF, markeredgewidth=1.0)
        for k in range(4): ax.text(k, m[k] + (0.55 if grid == '3x3' else 1.1), f'{m[k]:+.2f}', ha='center', fontsize=7, color=INK)
        ax.axhline(0, color=INK2, lw=0.8, ls='--', zorder=1)
        ax.set_xticks(range(4), ['K=1', 'K=2', 'K=3', 'iid']); ax.set_ylim(*yl); ax.set_xlim(-0.5, 3.5)
        if c == 0: ax.set_ylabel(f'{grid}: gain vs Z (%)')
        else: ax.tick_params(labelleft=False)
        mono = int(sum(np.all(np.diff(y) >= 0) for y in Y)); hz = int(sum(y[3] < y[0] for y in Y))
        ax.set_title(f'{grid} {name}', loc='left', fontsize=8.8)
        ax.text(0.02, 0.03, f'n = {len(S)} seeds; rising on {mono}/{len(S)}; iid < K1 on {hz}/{len(S)}', transform=ax.transAxes, fontsize=6.8, color=INK2)
        dump[f'{grid}|{fam}'] = dict(seeds=S, mean=m.tolist(), lo=lo, hi=hi, per_seed=Y.tolist(), monotone_up=mono, iid_below_K1=hz,
                                     panels={K: x['panels'] for K, x in zip(ORDER, cells)})
fig.text(0.01, -0.02, 'Thin lines: seeds (per-seed gain averaged over all finished panels containing the cell); bold: mean, band: 95 % seed bootstrap; shaded: training channel(s); '
         'dashed: zero-byte student Z.\n"rising" = non-decreasing over the four channels; 3x3 single-panel receivers: CK2 (3901), MIX2 (4501); 4x4 MIX: test D (4601).', fontsize=7, color=INK2)
save(fig, 'F4_shapes')
json.dump(dump, open(OUT / 'F4_data.json', 'w'), indent=1)
for k, v in dump.items(): print(k, [round(x, 2) for x in v['mean']], 'rising', v['monotone_up'], '/', len(v['seeds']), 'iid<K1', v['iid_below_K1'])
