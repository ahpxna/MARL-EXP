#!/usr/bin/env python3
"""B6-SL report (PROTOCOL_CITY_B6 §B6-SL, registered 04/10/2026 wake 8 before the run): σ-fleet upgrade under the frozen learned light.
Rows: wave2_20261004/049l, tags S<σ>_<light> with light in ACT, RL-H-0..3.  Crossed bootstrap light-seed x traffic (the wave-2 helpers)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402

D = R.W / '049l'; L = [f'RL-H-{i}' for i in range(4)]; SEL = R.SEL


def main():
    Rt = {}
    for f in D.glob('*.json'):
        x = json.loads(f.read_text())
        if isinstance(x, dict) and 'rows' in x:
            for r in x['rows']:
                Rt[(f.stem, r['seed'])] = r
    need = [(f'S{sg}_{l}', s) for sg in ('0.5', '0.3', '0.0') for l in ['ACT'] + L for s in SEL]
    if any(k not in Rt for k in need):
        print('B6-SL INCOMPLETE', sum(k not in Rt for k in need), 'missing'); return
    v = lambda sg, l, s, k: Rt[(f'S{sg}_{l}', s)][k]
    fuel = lambda a, b, l, s: 100 * (v(a, l, s, 'fuel_agent') / v(b, l, s, 'fuel_agent') - 1)
    dr = R.draws((4, len(SEL))); out = ['== B6-SL σ-fleet upgrade under the frozen learned light (SELECT 100-104; light seeds RL-H_0..3)']
    for sg in ('0.3', '0.0'):
        lab = 'SL-1' if sg == '0.3' else 'SL-3'
        T = R.crossed(np.array([[v(sg, l, s, 'timeloss_agent') - v('0.5', l, s, 'timeloss_agent') for s in SEL] for l in L]), dr)
        F = R.crossed(np.array([[fuel(sg, '0.5', l, s) for s in SEL] for l in L]), dr)
        ta = np.mean([v(sg, 'ACT', s, 'timeloss_agent') - v('0.5', 'ACT', s, 'timeloss_agent') for s in SEL]); fa = np.mean([fuel(sg, '0.5', 'ACT', s) for s in SEL])
        out.append(f'{lab} σ {sg} - σ 0.5 under RL-H: agent TL {R.fmt(*T)}; agent fuel % {R.fmt(*F)} (under ACT: TL {ta:+.2f}, fuel {fa:+.2f} %)'
                   + (f' -> {"benefit KEPT" if T[2] < 0 and F[2] < 0 else "benefit NOT kept"}' if sg == '0.3' else ''))
        for k in ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel'):
            if k == 'fuel':
                cube = np.array([[fuel(sg, '0.5', l, s) - fuel(sg, '0.5', 'ACT', s) for s in SEL] for l in L])
            else:
                cube = np.array([[(v(sg, l, s, k) - v('0.5', l, s, k)) - (v(sg, 'ACT', s, k) - v('0.5', 'ACT', s, k)) for s in SEL] for l in L])
            p, ci, up = R.crossed(cube, dr); lab2 = 'SL-2' if sg == '0.3' else 'SL-3'
            ver = ''
            if sg == '0.3' and k == 'timeloss':
                ver = f' -> {"SUPPORTED (|interaction| < 0.5: no partner-specificity to the driver model)" if ci[0] > -0.5 and ci[1] < 0.5 else "NOT SUPPORTED"}'
            out.append(f'  {lab2} interaction [{k}{" %" if k == "fuel" else ""}] (σ{sg} - σ0.5)|RL-H - (σ{sg} - σ0.5)|ACT: {R.fmt(p, ci)}{ver}')
        gain = lambda sgx: np.mean([[v(sgx, l, s, 'timeloss') - v(sgx, 'ACT', s, 'timeloss') for s in SEL] for l in L])
        out.append(f'  light-upgrade gain RL-H - ACT (city TL): fleet σ0.5 {gain("0.5"):+.2f}; fleet σ{sg} {gain(sg):+.2f}')
    txt = '\n'.join(out) + '\n'; (R.W / 'report_b6sl.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main()
