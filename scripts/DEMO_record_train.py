#!/usr/bin/env python3
"""Demo: record a training run for the browser replay (10/10/2026).  Patches scripts.CITY_env.run_episode (before the trainer imports it) to
count episodes; in the episodes listed in DEMO_EPISODES (0-based, comma-separated) it stores, between DEMO_T0 and DEMO_T1 simulated seconds,
every vehicle's position (0.1 m), heading, speed (0.1 m/s) and fleet membership (cars.is_agent when the trainer has a fleet, else 0) and
every signal's state.  Training itself is untouched and deterministic, so the final checkpoint can be compared with the saved one.
Output: $DEMO_OUT (json: episodes [{ep, frames}], tls).   Usage: DEMO_record_train.py scripts/<trainer>.py <its args>"""
import json, os, runpy, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402

T0, T1 = float(os.environ.get('DEMO_T0', 600)), float(os.environ.get('DEMO_T1', 720)); OUTF = os.environ['DEMO_OUT']
EPS = {int(x) for x in os.environ['DEMO_EPISODES'].split(',')}
ST = dict(ep=-1, rec=[], tls=None); _rep = CE.run_episode


def run_episode(net, rou, seed, light=None, cars=None, **kw):
    ST['ep'] += 1; ep = ST['ep']
    if ep not in EPS:
        return _rep(net, rou, seed, light, cars, **kw)
    inner = light; frames = []; ids = {}

    class Rec:
        def step(self, t):
            if inner is not None:
                inner.step(t)
            if T0 <= t < T1:
                ls = CE.ls
                if ST['tls'] is None:
                    ST['tls'] = sorted(ls.trafficlight.getIDList())
                isag = getattr(cars, 'is_agent', None); veh = []; halted = 0; vs = 0.0
                for v in ls.vehicle.getIDList():
                    if v not in ids:
                        ids[v] = len(ids)
                    x, y = ls.vehicle.getPosition(v); sp = ls.vehicle.getSpeed(v); vs += sp; halted += sp < 0.1
                    veh.append([ids[v], int(round(x * 10)), int(round(y * 10)), int(round(ls.vehicle.getAngle(v))) % 360, int(round(sp * 10)),
                                int(bool(isag(v))) if isag else 0])
                frames.append(dict(t=int(t), v=veh, s=[ls.trafficlight.getRedYellowGreenState(i) for i in ST['tls']], h=halted,
                                   ms=round(vs / max(1, len(veh)), 2)))
    out = _rep(net, rou, seed, Rec(), cars, **kw)
    ST['rec'].append(dict(ep=ep, frames=frames))
    Path(OUTF).write_text(json.dumps(dict(t0=T0, t1=T1, tls=ST['tls'], episodes=ST['rec']), separators=(',', ':')))
    print(f'DEMO recorded episode {ep} ({len(frames)} frames)', flush=True)
    return out


CE.run_episode = run_episode
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]; runpy.run_path(str(ROOT / target), run_name='__main__')
