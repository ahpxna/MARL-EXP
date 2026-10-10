#!/usr/bin/env python3
"""Trace check of the movement-specific SPaT feature (scripts/CITY_spat_feature.py).  Light FT (static programs) or ACT (actuated; the
program-based value is then only a NAIVE predictor and must be reported as such), traffic seed 100, 1800 s, every agent car in its
200 m zone every second: predicted green onset t + ttg (or green end t + ttr) vs the FIRST time the observed link state shows it.
FT verdict: PASS iff every prediction is exact (error 0) under the documented convention.  Descriptive for ACT.  No control is applied."""
import sys
from collections import defaultdict
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
from scripts.CITY_spat_feature import spat  # noqa: E402
import sumolib  # noqa: E402


def main(light, end=1800, seed=100):
    ls = CE.ls; net = Q7.NET_S if light == 'FT' else Q7.NET_A
    ls.start([sumolib.checkBinary('sumo'), '-n', net, '-r', Q7.ROU.format(seed), '--seed', str(seed), '--no-step-log', '--no-warnings', '--step-length', '1'])
    pend = []; events = defaultdict(list); last = {}; inval = 0; n = 0
    try:
        while ls.simulation.getTime() < end:
            ls.simulationStep(); t = ls.simulation.getTime()
            for tid in ls.trafficlight.getIDList():               # record link-level green onsets / ends at their FIRST observed time
                st = ls.trafficlight.getRedYellowGreenState(tid)
                for li, c in enumerate(st):
                    g = c in 'Gg'; key = (tid, li)
                    if key in last and last[key] != g:
                        events[(tid, li, 'on' if g else 'off')].append(t)
                    last[key] = g
            for v in ls.vehicle.getIDList():
                if CE._stable_u(seed, v) >= Q7.RHO:
                    continue
                nt = ls.vehicle.getNextTLS(v)
                if not nt or nt[0][2] > 200:
                    continue
                tid, li = nt[0][0], nt[0][1]; s = spat(tid, li); n += 1
                if not s['valid']:
                    inval += 1; continue
                if s['ttg'] > 0:
                    pend.append((tid, li, 'on', t, t + s['ttg']))
                elif s['ttr'] > 0:
                    pend.append((tid, li, 'off', t, t + s['ttr']))
    finally:
        ls.close()
    err = []; cens = 0; missing = 0
    for tid, li, kind, t0, pred in pend:
        nxt = [e for e in events[(tid, li, kind)] if e > t0]
        if pred >= end - 1:
            cens += 1                                              # censored: the predicted event lies at or beyond the trace end
        elif nxt:
            err.append(nxt[0] - pred)
        else:
            missing += 1                                           # predicted inside the trace but never observed: counted as an error
    print(f'{light}: predictions {len(pend)}: checked {len(err)}, censored at trace end {cens}, missing (predicted, never observed) {missing}')
    if not err:
        print(f'{light}: {n} agent-seconds in zone, {inval} invalid; no checkable prediction (feature unavailable for this light by design)'); return np.array([]), missing
    err = np.array(err); u, c = np.unique(np.round(err, 3), return_counts=True)
    print(f'{light}: {n} agent-seconds in zone, {inval} invalid; {len(err)} checked predictions; error (actual - predicted) values: '
          + ', '.join(f'{a:+g}s x{b}' for a, b in list(zip(u, c))[:12]) + (' ...' if len(u) > 12 else ''))
    print(f'{light}: mean |err| {np.abs(err).mean():.3f}, share exact {np.mean(err == 0):.4f}, max |err| {np.abs(err).max():.1f}')
    return err, missing


if __name__ == '__main__':
    bad = []
    for L in sys.argv[1:] or ['FT', 'ACT']:
        res = main(L)
        if L == 'FT':                                              # FT is the gate: >0 checked, every error 0, no missing event
            err, missing = res
            if len(err) == 0 or np.any(err != 0) or missing:
                bad.append(f'FT: checked {len(err)}, nonzero errors {int(np.sum(err != 0)) if len(err) else "n/a"}, missing {missing}')
    print('SPAT TRACE CHECK', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
