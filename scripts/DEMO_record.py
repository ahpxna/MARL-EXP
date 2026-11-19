#!/usr/bin/env python3
"""Demo recorder (10/10/2026): records one evaluator run second by second for a browser replay.  Wraps CITY_eval4.run_episode (any evaluator
run through CITY_w9_run / CITY_w20_run) and, between DEMO_T0 and DEMO_T1 simulated seconds, stores for every vehicle on the network its
position (0.1 m), heading, speed (0.1 m/s) and whether it belongs to the SPaT-following fleet (u(seed, id) < rho), and for every signal its
red-yellow-green state string.  Per-second network counters: vehicles, halted vehicles, mean speed.  Output: $DEMO_OUT (json).
Usage: CITY_w9_run.py none scripts/CITY_w20_run.py scripts/DEMO_record.py scripts/CITY_eval_n4.py ... --seeds 1400 --tag X --out DIR"""
import json, os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402

T0, T1 = float(os.environ.get('DEMO_T0', 1200)), float(os.environ.get('DEMO_T1', 1500)); OUTF = os.environ['DEMO_OUT']
ST = dict(seed=0); _run = E4.run


def run(a, seed, end):
    ST['seed'] = int(seed); return _run(a, seed, end)


E4.run = run
_rep = E4.run_episode


def run_episode(net, rou, seed, light, cars, **kw):
    inner = light; ids = {}; frames = []; tls_ids = None

    class Rec:
        def step(self, t):
            nonlocal tls_ids
            if inner is not None:
                inner.step(t)
            if T0 <= t < T1:
                ls = CE.ls
                if tls_ids is None:
                    tls_ids = sorted(ls.trafficlight.getIDList())
                veh = []; halted = 0; vs = 0.0
                for v in ls.vehicle.getIDList():
                    if v not in ids:
                        ids[v] = len(ids)
                    x, y = ls.vehicle.getPosition(v); sp = ls.vehicle.getSpeed(v); vs += sp; halted += sp < 0.1
                    veh.append([ids[v], int(round(x * 10)), int(round(y * 10)), int(round(ls.vehicle.getAngle(v))) % 360, int(round(sp * 10)),
                                int(CE._stable_u(ST['seed'], v) < Q7.RHO)])
                frames.append(dict(t=int(t), v=veh, s=[ls.trafficlight.getRedYellowGreenState(i) for i in tls_ids], n=len(veh), h=halted,
                                   ms=round(vs / max(1, len(veh)), 2)))
    out = _rep(net, rou, seed, Rec(), cars, **kw)
    Path(OUTF).write_text(json.dumps(dict(t0=T0, t1=T1, seed=seed, tls=tls_ids, frames=frames), separators=(',', ':')))
    print('DEMO recorded', len(frames), 'frames ->', OUTF, flush=True)
    return out


E4.run_episode = run_episode
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
