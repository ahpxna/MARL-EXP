#!/usr/bin/env python3
"""Correctness trace of reward v3 (user audit Addendum B6 item 4; 04/10/2026 wake 3).  Runs CarRLv3 (scripts/CITY_fleet_train_v3.py,
unchanged) with random commands, an INDEPENDENT per-second logger of every agent vehicle (speed, allowed speed, fuel rate), and the setSpeed
spy of CITY_v2_trace_check for transition ownership (CarRLv3 appends a non-terminal transition just before setSpeed(v, nv >= 0) and a
terminal one just after setSpeed(v, -1)).  Checks and COUNTS (conventions are reported, not hidden):
  non-terminal   r == -[(1 - v/v_allowed) + 0.5 * fuel / 1000] from the logger at the closing second (v, fuel of the vehicle then)
  terminal       same at the closing second; ARRIVED cars: cost 0 by convention (counted)
  api-zero       transitions whose cost is exactly 0 because SUMO could not be read (convention; counted)
  gap            the closing decision is not one second after the command (teleport / re-entry; counted)
  truncated      decisions still open at the end of the horizon (no transition written; counted)
Consistency with SUMO counters (NOT an identity claim; the reward only covers the approach zone, while tripinfo is the whole trip):
  for finished agent trips, sum over the trip of the logged fuel rate x 1 s vs tripinfo fuel_abs, and of (1 - v/v_allowed) vs timeLoss
  (SUMO's timeLoss uses its own ideal speed, including speedFactor; https://sumo.dlr.de/docs/Simulation/Output/TripInfo.html).
The step length is 1 s, so a fuel rate in mg/s integrates to mg per step."""
from __future__ import annotations
import argparse, json, os, sys, tempfile
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, run_episode, read_tripinfo, ACC  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_fleet_train_v3 as V3  # noqa: E402


class Traced(V3.CarRLv3):
    def __init__(self, *a, **k):
        super().__init__(*a, **k); self.calls = []; self.meta = []; self.t = 0
        outer = self

        class L(list):
            def append(self, x):
                outer.meta.append((outer.t, len(outer.calls))); super().append(x)
        self.trans = L()

    def step(self, t):
        self.t = t; super().step(t)


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    res = []
    for light_s in a.lights:
        for seed in a.seeds:
            info = NetInfo(Q7.NET_S); net, lck, mg = X2.light_spec(light_s)
            light = LightRL(info, Q7.load_policy(lck), max_g=mg) if lck is not None else None
            rng = np.random.default_rng(seed); cars = Traced(lambda O: rng.integers(0, len(ACC), len(O)), Q7.RHO, seed, record=True)
            log = {}; tele = set(); orig = CE.ls.vehicle.setSpeed

            def spy(v, val, cars=cars, orig=orig):
                cars.calls.append((cars.t, v, float(val))); return orig(v, val)

            class Log:
                def step(self, t):
                    ls = CE.ls; tele.update(ls.simulation.getStartingTeleportIDList())
                    for v in ls.vehicle.getIDList():
                        if cars.is_agent(v):
                            log[(t, v)] = (ls.vehicle.getSpeed(v), ls.vehicle.getAllowedSpeed(v), ls.vehicle.getFuelConsumption(v))
            ctrl = [c for c in (light, cars, Log()) if c is not None]

            class Multi:
                def step(self, t):
                    for c in ctrl:
                        c.step(t)
            fd, ti = tempfile.mkstemp(suffix='.xml', dir=os.environ.get('XPLAY_TMP')); os.close(fd)
            CE.ls.vehicle.setSpeed = spy
            try:
                run_episode(net, Q7.ROU.format(seed), seed, Multi(), None, end=a.end, tripinfo=ti)
            finally:
                CE.ls.vehicle.setSpeed = orig
            trips = read_tripinfo(ti); os.remove(ti)
            cost = lambda x: (max(0.0, 1.0 - x[0] / x[1]) if x[1] > 0 else 1.0) + V3.KAPPA * x[2] / 1000.0
            c = dict(nonterm_ok=0, nonterm_bad=0, term_ok=0, term_bad=0, term_arrived_zero=0, api_zero=0, gap=0, unattributed=0, owner_teleported=0)
            cmd_times = {}
            for i, (tc, v, val) in enumerate(cars.calls):
                if val >= 0:
                    cmd_times.setdefault(v, []).append((i, tc))
            for k, (po, pa, r, o, done) in enumerate(cars.trans):
                tc, pos = cars.meta[k]
                if done:
                    if pos == 0 or cars.calls[pos - 1][2] != -1.0:
                        c['unattributed'] += 1; continue
                    v = cars.calls[pos - 1][1]; x = log.get((tc, v))
                    if x is None:                               # arrived: CarRLv3._end(arrived=True) charges 0 by convention
                        c['term_arrived_zero'] += 1; ok = r == 0.0
                    else:
                        ok = abs(r + cost(x)) < 1e-9
                    c['term_ok' if ok else 'term_bad'] += 1
                else:
                    if pos >= len(cars.calls) or cars.calls[pos][2] < 0:
                        c['unattributed'] += 1; continue
                    v = cars.calls[pos][1]; x = log.get((tc, v))
                    prev = [tt for (ii, tt) in cmd_times.get(v, []) if ii < pos]
                    if not prev or tc - prev[-1] != 1.0:
                        c['gap'] += 1
                    if x is None:
                        c['api_zero'] += r == 0.0; ok = r == 0.0
                    else:
                        ok = abs(r + cost(x)) < 1e-9
                    c['nonterm_ok' if ok else 'nonterm_bad'] += 1
                c['owner_teleported'] += v in tele
            c['truncated_open'] = len(cars.state); c['teleports'] = len(tele)
            fin = [t for t in trips if t['finished'] and cars.is_agent(t['id'])]; fe = []; te = []
            for t in fin:
                xs = [x for (tt, v), x in log.items() if v == t['id']]
                if xs and t['fuel'] > 0:
                    fe.append(sum(x[2] for x in xs) / t['fuel'] - 1); te.append(sum(max(0.0, 1 - x[0] / x[1]) if x[1] > 0 else 1.0 for x in xs) - t['timeloss'])
            c['fuel_sum_vs_tripinfo_rel_median'] = float(np.median(fe)) if fe else None; c['fuel_rel_abs_p95'] = float(np.percentile(np.abs(fe), 95)) if fe else None
            c['timeloss_sum_minus_tripinfo_median_s'] = float(np.median(te)) if te else None; c['finished_agent_trips'] = len(fin)
            res.append(dict(light=light_s, seed=seed, **c)); print(light_s, seed, c, flush=True)
    ok = all(r['nonterm_bad'] == 0 and r['term_bad'] == 0 and r['unattributed'] == 0 for r in res)
    Path(a.out).parent.mkdir(parents=True, exist_ok=True)
    Path(a.out).write_text(json.dumps(dict(rows=res, verdict='PASS' if ok else 'FAIL'), indent=1)); print('VERDICT', 'PASS' if ok else 'FAIL')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--lights', nargs='+', default=['ACT', 'FT']); p.add_argument('--seeds', type=int, nargs='+', default=[100])
    p.add_argument('--end', type=float, default=5400); p.add_argument('--out', required=True)
    main(p.parse_args())
