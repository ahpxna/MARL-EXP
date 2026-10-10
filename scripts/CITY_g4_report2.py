#!/usr/bin/env python3
"""G4-L2 report (PROTOCOL_CITY_G4_COLOGNE8_20261004 §G4-L2, written before the run).  stage 'g41': RLK480 - FT on 100-109 (eval/ + eval480/);
stage 'tv': G4-2' / G4-3' on 110-129 (eval480b/), only if g41 passed (file eval480/G41_PASS)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402

G = Path(__file__).resolve().parents[1] / 'research/city_sim/g4_cologne8'; RL = ['RLK480_s11', 'RLK480_s12']


def rows(*ds):
    Rt = {}
    for d in ds:
        for f in Path(d).glob('*.json'):
            for r in json.loads(f.read_text()).get('rows', []):
                Rt[(f.stem, r['seed'])] = r
    return Rt


def g41():
    S = list(range(100, 110)); Rt = rows(G / 'eval', G / 'eval480')
    c = np.array([[Rt[(f'{l}_base', s)]['timeloss'] - Rt[('FT_base', s)]['timeloss'] for s in S] for l in RL])
    p = R.crossed(c, R.draws((2, len(S)))); ok = p[2] < 0
    txt = f"G4-1' RLK480 - FT city TL (100-109): {R.fmt(*p)} -> {'SUPPORTED' if ok else 'NOT SUPPORTED (G4 stops)'}\n"
    (G / 'eval480' / 'report_g41.txt').write_text(txt); print(txt)
    if ok:
        (G / 'eval480' / 'G41_PASS').write_text('1\n')


def tv():
    S = list(range(110, 130)); Rt = rows(G / 'eval480b'); dr = R.draws((2, len(S))); out = []
    v = lambda l, fl, s: Rt[(f'{l}_{fl}', s)]['timeloss']
    ok0 = all(abs(v(l, 'ctrl', s) - v(l, 'base', s)) < 1e-9 for l in ['FT'] + RL for s in S); out.append(f"G4-0' ctrl == base: {'PASS' if ok0 else 'FAIL (void)'}")
    for lab, fl in (("G4-2' σ0.3", 'sig0.3'), ("G4-3' ACC", 'acc')):
        c = np.array([[(v(l, fl, s) - v(l, 'base', s)) - (v('FT', fl, s) - v('FT', 'base', s)) for s in S] for l in RL]); p, ci, up = R.crossed(c, dr)
        out.append(f'{lab} interaction (city TL, 110-129): {R.fmt(p, ci, up)} -> {"NO HARM (upper < +0.5)" if up < 0.5 else "HARM NOT EXCLUDED"}')
    g = np.array([[v(l, 'base', s) - v('FT', 'base', s) for s in S] for l in RL]); out.append(f'(reported) RLK480 - FT on 110-129: {R.fmt(*R.crossed(g, dr))}')
    txt = '\n'.join(out) + '\n'; (G / 'eval480b' / 'report_g4tv2.txt').write_text(txt); print(txt)


if __name__ == '__main__':
    {'g41': g41, 'tv': tv}[sys.argv[1]]()
