#!/usr/bin/env python3
"""W15-4 (PROTOCOL_CITY_WAVE15_20261007, Amendment A1): the projected-queue adapter.  Replaces, in the learned light's observation, the
halting count of each served lane group by
    h_pq = #{v on the group's lanes : speed < 0.1}  +  #{moving v : (lane length - lane position) / speed <= tau}
(vehicle counts, phase, spent time and every other input unchanged).  Patches CITY_env.LightRL.obs (two-green RL-H lights, grid4 / rand3)
and CITY_lightk.LightRLK.obs (multi-green spider lights); no file is edited.  Use with the stock adapters switched off (--light-obs q:0:0,
or RLKQ:<ckpt>:0:0) so that no second transform is applied.  tau = 0 reproduces the raw light exactly (self-check KPQ-1).
Env W15_PQ=<tau seconds>.  Rows get w15_pq.  Usage: W15_PQ=10 CITY_w15_pq.py <target script> <its args>"""
import os, runpy, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_lightk as LK  # noqa: E402
import scripts.CITY_eval4 as E4  # noqa: E402
TAU = float(os.environ['W15_PQ']); _LEN = {}


def hpq(lanes):
    ls = CE.ls; c = 0
    for l in lanes:
        L = _LEN.get(l)
        if L is None:
            L = _LEN[l] = ls.lane.getLength(l)
        for v in ls.lane.getLastStepVehicleIDs(l):
            sp = ls.vehicle.getSpeed(v)
            if sp < 0.1 or (TAU > 0 and (L - ls.vehicle.getLanePosition(v)) / sp <= TAU):
                c += 1
    return c


def halt(lanes):
    return sum(CE.ls.lane.getLastStepHaltingNumber(l) for l in lanes)


def obs2(self, tid):
    ls = CE.ls; d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid)
    h = [hpq(s) for s in d['serve']]; n = [sum(ls.lane.getLastStepVehicleNumber(l) for l in s) for s in d['serve']]
    cur = d['greens'].index(ph) if ph in d['greens'] else -1
    return np.array([h[0] / 10, h[1] / 10, n[0] / 20, n[1] / 20, cur == 0, cur == 1, ls.trafficlight.getSpentDuration(tid) / 60], np.float32), \
        sum(halt(s) for s in d['serve']), cur


def obsk(self, tid):
    ls = CE.ls; d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid)
    if ph not in d['greens']:
        return None, 0, -1
    cur = d['greens'].index(ph); k = len(d['greens']); nxt = (cur + 1) % k
    n = lambda s: sum(ls.lane.getLastStepVehicleNumber(l) for l in s)  # noqa: E731
    o = np.array([hpq(d['serve'][cur]) / 10, hpq(d['serve'][nxt]) / 10, n(d['serve'][cur]) / 20, n(d['serve'][nxt]) / 20, cur / max(1, k - 1),
                  ls.trafficlight.getSpentDuration(tid) / 60, float(nxt == 0)], np.float32)
    return o, sum(halt(s) for s in d['serve']), cur


CE.LightRL.obs = obs2; LK.LightRLK.obs = obsk
_run = E4.run


def run(a, seed, end):
    out = _run(a, seed, end); out['w15_pq'] = TAU; return out


E4.run = run
E4.SRC = f"{getattr(E4, 'SRC', '')}+w15pq:{TAU}"
if __name__ == '__main__':
    target = sys.argv[1]; sys.argv = [target] + sys.argv[2:]
    runpy.run_path(str(ROOT / target), run_name='__main__')
