#!/usr/bin/env python3
"""Teleport diagnostic for the GLOSA family (04/10/2026, after C-44; a diagnostic, not an endpoint).  One FT episode on traffic SEED with
the fleet GLOSA∘σ* (base sigma 0.3) or plain GLOSA (base 0.5), both theta0 = (0, 0, 200) via the frozen CarESGlosa / CarESGlosaS classes.
Every speed command of the fleet is recorded (ls.vehicle.setSpeed wrapped).  When a vehicle starts teleporting, its last snapshot (taken
the step before, for every vehicle waiting >= 200 s) and the chain of its leaders (now) are printed: agent?, last command, speed, waiting
time, lane / position / lane length, the lane change it still needs (best-lanes offset, continuation), and its next signal link state.
Usage: CITY_teleport_diag.py SEED {sbase,plain}
diag2 variant: any eval6 fleet spec (e.g. P:<fleet.pt>, R:<fleet.pt>, IC:GLOSA), built through CITY_eval6.load_fleet with guard 'none'.
Usage: CITY_teleport_diag2.py SEED SPEC"""
import os, sys, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_es_glosa as ES  # noqa: E402
import scripts.CITY_es_glosa_sbase as S  # noqa: E402,F401
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6 as E6  # noqa: E402,F401

SEED, MODE = int(sys.argv[1]), sys.argv[2]
cars = E4.load_fleet(MODE, SEED, 'none')[0]
ls = CE.ls; CMD = {}; SNAP = {}; OUT = []
_set = ls.vehicle.setSpeed


def set_speed(v, x):
    CMD[v] = (ls.simulation.getTime(), round(float(x), 2)); _set(v, x)


ls.vehicle.setSpeed = set_speed


def info(v):
    try:
        ln = ls.vehicle.getLaneID(v); pos = ls.vehicle.getLanePosition(v); L = ls.lane.getLength(ln) if ln else -1
        off, cont = None, None
        for b in ls.vehicle.getBestLanes(v):
            if b[0] == ln:
                off, cont = b[3], b[4]
        nt = ls.vehicle.getNextTLS(v); nt = (nt[0][0], nt[0][1], round(nt[0][2], 1), nt[0][3]) if nt else None
        lead = ls.vehicle.getLeader(v, 100.0)
        return dict(v=v, agent=cars.is_agent(v), cmd=CMD.get(v), sp=round(ls.vehicle.getSpeed(v), 2), wait=round(ls.vehicle.getWaitingTime(v)),
                    lane=ln, pos=round(pos, 1), L=round(L, 1), lc_offset=off, cont=cont, tls=nt, leader=(lead[0], round(lead[1], 1)) if lead and lead[0] else None)
    except Exception as e:                                         # noqa: BLE001
        return dict(v=v, err=str(e)[:60])


inner = cars.step


def step(t):
    inner(t)
    for v in ls.simulation.getStartingTeleportIDList():
        OUT.append(f'[t={t:.0f}] TELEPORT {v}  last snapshot: {SNAP.get(v)}')
        s = SNAP.get(v); seen = {v}; hop = s['leader'][0] if s and s.get('leader') else None
        while hop and hop not in seen and len(seen) < 16:
            seen.add(hop); x = info(hop); OUT.append(f'      leader chain: {x}'); hop = x['leader'][0] if x.get('leader') else None
    for v in ls.vehicle.getIDList():
        if ls.vehicle.getWaitingTime(v) >= 200:
            SNAP[v] = info(v)


cars.step = step

if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'
    fd, ti = tempfile.mkstemp(suffix='.xml', dir=os.environ.get('XPLAY_TMP')); os.close(fd)
    m = CE.run_episode(Q7.NET_S, Q7.ROU.format(SEED), SEED, None, cars, end=5400, tripinfo=ti); os.remove(ti)
    print(f'== seed {SEED} {MODE}: teleports {m["teleports"]}, fleet commands {len(CMD)} vehicles')
    print('\n'.join(OUT), flush=True)
