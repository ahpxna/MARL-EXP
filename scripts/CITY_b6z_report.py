#!/usr/bin/env python3
"""B6-Z report (PROTOCOL_CITY_B6 §B6-Z, registered 09:00 04/10/2026, written before the run): null fleets vs always-SUMO, ACT, SELECT
100-104, directory wave2_20261004/046z.  Z-1 exact identity of Z-rel; Z-2 Z-res0 agent TL crossed 95 % CI inside [-0.5, +0.5];
Z-3 Z-hold descriptive; Z-4a Z-sig0 (SUMO driver, sigma 0, CITY_eval4_sig0) vs always-SUMO on SELECT and on 400-409 (046z/T);
Z-4b every B6-T fleet (046) minus Z-sig0 on 400-409, agent TL one-sided 95 % upper and fuel %.  Bootstrap: the wave-2 reporter's draws / crossed (traffic resampled, 2000 draws, rng 0).
Usage: CITY_b6z_report.py [DIR] (default the registered directory; a smoke directory may be passed)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402

KEYS = ('timeloss_agent', 'timeloss_human', 'timeloss', 'fuel_agent', 'teleports', 'unfinished')


def load(d):
    Rt = {}
    for f in d.glob('*.json'):
        x = json.loads(f.read_text())
        if isinstance(x, dict) and 'rows' in x:
            for r in x['rows']:
                Rt[(f.stem, r['seed'])] = r
    return Rt


def vs(out, lab, A, B, seeds, dr):
    g = lambda k: np.array([A[s][k] - B[s][k] for s in seeds])
    T = R.crossed(g('timeloss_agent'), dr); H = R.crossed(g('timeloss_human'), dr); C = R.crossed(g('timeloss'), dr)
    F = R.crossed(np.array([100 * (A[s]['fuel_agent'] / B[s]['fuel_agent'] - 1) for s in seeds]), dr)
    out.append(f'{lab}: agent TL {R.fmt(*T)}; agent fuel % {R.fmt(*F)}; human TL {R.fmt(*H)}; city TL {R.fmt(*C)}')
    return T


def z4(out, d):
    S = load(d); seeds = sorted(s for (k, s) in S if k == 'Z-sig0_ACT'); dr = R.draws((len(seeds),))
    if seeds and all(('OFF_ACT', s) in S for s in seeds):
        vs(out, f'Z-4a SELECT Z-sig0 - always-SUMO', {s: S[('Z-sig0_ACT', s)] for s in seeds}, {s: S[('OFF_ACT', s)] for s in seeds}, seeds, dr)
    T = load(d / 'T'); B = load(R.W / '046'); ts = list(range(400, 410))
    if not all(('Z-sig0_ACT', s) in T and ('OFF_ACT', s) in B for s in ts):
        out.append('Z-4a/b on 400-409 INCOMPLETE (046z/T or 046 missing)'); return
    dr = R.draws((len(ts),)); Z = {s: T[('Z-sig0_ACT', s)] for s in ts}
    vs(out, 'Z-4a 400-409 Z-sig0 - always-SUMO', Z, {s: B[('OFF_ACT', s)] for s in ts}, ts, dr)
    for F in sorted({k for (k, s) in B if k.startswith('U-')}):
        if all((F, s) in B for s in ts):
            t = vs(out, f'Z-4b {F} - Z-sig0', {s: B[(F, s)] for s in ts}, Z, ts, dr)
            out.append(f'     -> {"faster than the perfect SUMO driver (upper < 0)" if t[2] < 0 else "NOT faster than the perfect SUMO driver (upper >= 0)"}')


def main(d):
    Rt = {}
    for f in d.glob('*.json'):
        x = json.loads(f.read_text())
        if isinstance(x, dict) and 'rows' in x:
            for r in x['rows']:
                Rt[(f.stem, r['seed'])] = r
    seeds = sorted({s for (k, s) in Rt if k == 'OFF_ACT'}); out = [f'== B6-Z null fleets vs always-SUMO, ACT, traffic {seeds} ({d})']
    if not seeds or any((f'{z}_ACT', s) not in Rt for z in ('Z-rel', 'Z-res0', 'Z-hold') for s in seeds):
        out.append('B6-Z INCOMPLETE'); print('\n'.join(out)); return
    dr = R.draws((len(seeds),))
    dif = {k: max(abs(Rt[('Z-rel_ACT', s)][k] - Rt[('OFF_ACT', s)][k]) for s in seeds) for k in KEYS}
    z1 = all(v < 1e-9 for v in dif.values())
    out.append(f'Z-1 Z-rel == always-SUMO: max |diff| per quantity {dif} -> {"SUPPORTED (exact)" if z1 else "NOT SUPPORTED (release path differs from SUMO)"}')
    for z in ('Z-res0', 'Z-hold'):
        g = lambda k: np.array([Rt[(f'{z}_ACT', s)][k] - Rt[('OFF_ACT', s)][k] for s in seeds])
        T = R.crossed(g('timeloss_agent'), dr); H = R.crossed(g('timeloss_human'), dr); C = R.crossed(g('timeloss'), dr)
        F = R.crossed(np.array([100 * (Rt[(f'{z}_ACT', s)]['fuel_agent'] / Rt[('OFF_ACT', s)]['fuel_agent'] - 1) for s in seeds]), dr)
        line = f'{z}: agent TL {R.fmt(*T)}; agent fuel % {R.fmt(*F)}; human TL {R.fmt(*H)}; city TL {R.fmt(*C)}'
        if z == 'Z-res0':
            ok = T[1][0] > -0.5 and T[1][1] < 0.5
            line = 'Z-2 ' + line + f' -> {"SUPPORTED (residual class contains SUMO within 0.5)" if ok else "NOT SUPPORTED (delta = 0 is not SUMO: the residual class does not contain the baseline)"}'
        else:
            line = 'Z-3 (descriptive) ' + line
        out.append(line)
    z4(out, d)
    txt = '\n'.join(out) + '\n'; (d / 'report_b6z.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    main(Path(sys.argv[1]) if len(sys.argv) > 1 else R.W / '046z')
