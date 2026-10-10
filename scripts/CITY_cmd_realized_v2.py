#!/usr/bin/env python3
"""Behavioural diagnostic of commanded vs realized speed, VERSION 2 (audit item 5 / W-C, 04/10/2026 wake 3).  Fixes of v1
(scripts/CITY_cmd_realized.py, kept): the command is read EXACTLY from the fleet's own setSpeed call (cap = getAllowedSpeed, not 99, and no
float32 reconstruction); the realized cost changes ONLY the idle indicator (the acceleration term nv - sp is the same in both costs), so
cost_cmd - cost_real isolates the idle loophole.  Fleet unchanged (plain CarRL; any fleet spec of CITY_eval3).  Run with PYTHONHASHSEED=0."""
from __future__ import annotations
import argparse, json, os, sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, run_episode, IDLE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_eval3 as E3  # noqa: E402


def run(light_s, fleet_s, seed, end=5400):
    info = NetInfo(Q7.NET_S); net, lck, mg = X2.light_spec(light_s)
    light = LightRL(info, Q7.load_policy(lck), max_g=mg) if lck is not None else None
    cars, _ = E3.load_fleet(fleet_s, seed, 'none'); calls = []; spd = {}; tnow = [0]
    orig = CE.ls.vehicle.setSpeed

    def spy(v, val):
        if val >= 0:
            calls.append((tnow[0], v, float(val), CE.ls.vehicle.getSpeed(v)))
        return orig(v, val)

    class Log:
        def step(self, t):
            for v in cars.agents:
                try:
                    spd[(t, v)] = CE.ls.vehicle.getSpeed(v)
                except Exception:
                    pass

    class Multi:
        def step(self, t):
            tnow[0] = t
            for c in (light, cars, Log()):
                if c is not None:
                    c.step(t)
    CE.ls.vehicle.setSpeed = spy
    try:
        run_episode(net, Q7.ROU.format(seed), seed, Multi(), None, end=end)
    finally:
        CE.ls.vehicle.setSpeed = orig
    R = [(nv, sp, spd.get((t + 1, v))) for t, v, nv, sp in calls]; R = [x for x in R if x[2] is not None]
    nv = np.array([x[0] for x in R]); sp = np.array([x[1] for x in R]); vr = np.array([x[2] for x in R]); acc = 0.05 * (nv - sp) ** 2
    ia = (nv >= 0.1) & (vr < 0.1)
    return dict(light=light_s, fleet=fleet_s, seed=seed, commands=len(R), idle_cmd=float((nv < 0.1).mean()), idle_real=float((vr < 0.1).mean()),
                idle_avoided_of_real_idle=float(ia.sum() / max(1, (vr < 0.1).sum())), stopped_accel=float(((sp < 0.1) & (nv > sp + 1e-9)).sum() / max(1, (sp < 0.1).sum())),
                cost_cmd=float((1 + acc + IDLE * (nv < 0.1)).sum()), cost_real_idle_only=float((1 + acc + IDLE * (vr < 0.1)).sum()))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--configs', nargs='+', required=True); p.add_argument('--seeds', type=int, nargs='+', default=[100, 101]); p.add_argument('--out', required=True)
    a = p.parse_args()
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    rows = []
    for L, F in [x.split('/') for x in a.configs]:
        for s in a.seeds:
            r = run(L, F, s); rows.append(r); print(json.dumps(r), flush=True)
    Path(a.out).write_text(json.dumps(rows, indent=1))
