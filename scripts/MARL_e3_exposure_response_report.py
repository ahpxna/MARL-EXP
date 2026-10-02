#!/usr/bin/env python3
"""Exposure-response of decision flips against Z on the 3×3 development panel (EXPLORATORY; PROTOCOL_E3_G4_CONSTK_ADDENDUM1,
reported item).  Per receiver-step b3 = sum_j (a_j - 3)+ (scripts/MARL_e3_viewstats_probe_v2.py).  P(flip_Z | b3 bin), pooled
and by regime: if regimes agree at equal burden, burden rather than K organises the decision failures."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); D = M / 'e3_viewstats_v2_20261001'
BINS = [(0, 0), (1, 2), (3, 5), (6, 9), (10, 14), (15, 99)]


def main():
    F = {}
    for K in (0, 1, 2, 3):
        parts = []
        for s in range(10):
            d = D / f's{s}_K{K}'
            if not (d / 'manifest.json').exists():
                print('INCOMPLETE', d.name); return
            z = np.load(d / 'flags.npz'); parts.append(dict(b3=z['b3'], flip=z['zok'] & ~z['protoS'], bad=~z['protoS'], zbad=~z['zok']))
        F[K] = {k: np.concatenate([p[k] for p in parts]) for k in parts[0]}
    L = ['b3 bin | pooled flip_Z (n) | iid | K=1 | K=2 | K=3   (flip_Z = Z acceptable, relay not)']
    out = {}
    for lo, hi in BINS:
        cells = []
        allf = np.concatenate([F[K]['flip'][(F[K]['b3'] >= lo) & (F[K]['b3'] <= hi)] for K in F])
        for K in (0, 1, 2, 3):
            sel = (F[K]['b3'] >= lo) & (F[K]['b3'] <= hi)
            cells.append(f'{F[K]["flip"][sel].mean():.3f} ({int(sel.sum())})' if sel.sum() >= 50 else f'- ({int(sel.sum())})')
            out[f'{lo}-{hi}_K{K}'] = dict(n=int(sel.sum()), flip=float(F[K]['flip'][sel].mean()) if sel.any() else None)
        L.append(f'{lo}-{hi} | {allf.mean():.3f} ({len(allf)}) | ' + ' | '.join(cells))
    text = '\n'.join(L); print(text)
    (M / 'e3_exposure_response_report_20261001.json').write_text(json.dumps(out, indent=1))
    (M / 'e3_exposure_response_report_20261001.txt').write_text('EXPLORATORY\n' + text + '\n')


if __name__ == '__main__':
    main()
