#!/usr/bin/env python3
"""Report of PROTOCOL_E3_CROSS_STUDENT_FRAGILITY_20261001.md (EXPLORATORY)."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget')


def main():
    ov = json.loads((M / 'e3_overnight_report_20260930.json').read_text())['students']
    rows = []
    for fam, d in (('relay6_st', M / 'e3_cross_student_20261001'), ('relay6Clow_st', M / 'e3_cross_student_20261001'),
                   ('relay6Cage_st', M / 'e3_negflip_20261001')):
        for s in range(10):
            name = f'{fam}_s{s}'
            f = (d / name / 'flags.npz') if fam != 'relay6Cage_st' else (d / f's{s}_K1' / 'flags.npz')
            if name not in ov or not f.exists():
                continue
            z = np.load(f); nz = float(z['protoS'].mean() - z['zok'].mean())
            g = -np.mean([ov[name]['prefix/cap4']['vsZ'][0], ov[name]['prefix/low']['vsZ'][0]])
            ga = -np.mean([ov[name]['agefirst/cap4']['vsZ'][0], ov[name]['agefirst/low']['vsZ'][0]])
            rows.append((name, fam, nz, g, ga))
    L = [f'{n}: net_Z(K=1) {nz:+.3f} | congestion cap4/low gain {g:+.2f} % | age-first cap4/low gain {ga:+.2f} %' for n, _, nz, g, ga in rows]
    r_all = float(spearmanr([x[2] for x in rows], [x[3] for x in rows]).correlation)
    r_age = float(spearmanr([x[2] for x in rows], [x[4] for x in rows]).correlation)
    st = [x for x in rows if x[1] == 'relay6_st']
    r_st = float(spearmanr([x[2] for x in st], [x[3] for x in st]).correlation) if len(st) > 3 else float('nan')
    L += [f'Spearman(net_Z(K=1), congestion gain) over {len(rows)} students = {r_all:+.3f} (kill if < 0.3) -> {"SUPPORTED" if r_all >= 0.3 else "NOT SUPPORTED"}',
          f'  within relay6_st ({len(st)}): {r_st:+.3f}; with age-first cap4/low gain: {r_age:+.3f}']
    text = '\n'.join(L); print(text)
    (M / 'e3_cross_student_report_20261001.txt').write_text('EXPLORATORY\n' + text + '\n')


if __name__ == '__main__':
    main()
