#!/usr/bin/env python3
"""G4-TV report (PROTOCOL_CITY_G4_COLOGNE8_20261004, written before the run): directory research/city_sim/g4_cologne8/eval, tags <light>_<fleet>
with light in FT, RLK_s11, RLK_s12.  Crossed light-seed x SUMO-seed bootstrap (2000 draws, rng 0)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402

D = Path(__file__).resolve().parents[1] / 'research/city_sim/g4_cologne8/eval'; SEEDS = list(range(100, 110)); RL = ['RLK_s11', 'RLK_s12']


def main():
    Rt = {}
    for f in D.glob('*.json'):
        x = json.loads(f.read_text())
        for r in x.get('rows', []):
            Rt[(f.stem, r['seed'])] = r
    need = [(f'{l}_{fl}', s) for l in ['FT'] + RL for fl in ('base', 'sig0.3', 'ctrl', 'acc') for s in SEEDS]
    miss = [k for k in need if k not in Rt]; out = ['== G4-TV cologne8 (RESCO), SUMO seeds 100-109; lights FT and RLK (2 seeds)']
    if miss:
        out.append(f'INCOMPLETE ({len(miss)} missing)'); print('\n'.join(out)); return
    v = lambda l, fl, s, k: Rt[(f'{l}_{fl}', s)][k]
    ok0 = all(abs(v(l, 'ctrl', s, k) - v(l, 'base', s, k)) < 1e-9 for l in ['FT'] + RL for s in SEEDS for k in ('timeloss', 'timeloss_agent', 'fuel_agent'))
    out.append(f'G4-0 ctrl == base on every light and seed: {"PASS" if ok0 else "FAIL (report void)"}')
    if not ok0:
        print('\n'.join(out)); return
    dr = R.draws((2, len(SEEDS)))
    g1 = R.crossed(np.array([[v(l, 'base', s, 'timeloss') - v('FT', 'base', s, 'timeloss') for s in SEEDS] for l in RL]), dr)
    out.append(f'G4-1 (T1) RLK - FT city TL, base traffic: {R.fmt(*g1)} -> {"SUPPORTED (learned light beats FT)" if g1[2] < 0 else "NOT SUPPORTED"}')
    for lab, fl in (('G4-2 (T4) σ0.3', 'sig0.3'), ('G4-3 (T5) ACC', 'acc')):
        c = np.array([[(v(l, fl, s, 'timeloss') - v(l, 'base', s, 'timeloss')) - (v('FT', fl, s, 'timeloss') - v('FT', 'base', s, 'timeloss')) for s in SEEDS] for l in RL])
        p, ci, up = R.crossed(c, dr)
        d_ft = np.mean([v('FT', fl, s, 'timeloss') - v('FT', 'base', s, 'timeloss') for s in SEEDS])
        d_rl = np.mean([[v(l, fl, s, 'timeloss') - v(l, 'base', s, 'timeloss') for s in SEEDS] for l in RL])
        fa = np.mean([[100 * (v(l, fl, s, 'fuel_agent') / v(l, 'base', s, 'fuel_agent') - 1) for s in SEEDS] for l in ['FT'] + RL])
        out.append(f'{lab} interaction (city TL): {R.fmt(p, ci, up)} -> {"NO HARM (upper < +0.5)" if up < 0.5 else "HARM NOT EXCLUDED"}; '
                   f'fleet effect on city TL under FT {d_ft:+.2f}, under RLK {d_rl:+.2f}; agent fuel % (mean over lights) {fa:+.2f}')
    tel = {k: np.mean([v(l, fl, s, k) for l in ['FT'] + RL for fl in ('base', 'sig0.3', 'acc') for s in SEEDS]) for k in ('teleports', 'unfinished')}
    out.append(f'(reported) mean teleports {tel["teleports"]:.2f}, unfinished {tel["unfinished"]:.1f} per run')
    txt = '\n'.join(out) + '\n'; (D / 'report_g4tv.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main()
