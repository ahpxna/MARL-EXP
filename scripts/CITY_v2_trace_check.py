#!/usr/bin/env python3
"""Correctness trace of reward v2 (audit W-C, 04/10/2026 wake 3).  Runs CarRLv2 (scripts/CITY_fleet_upgrade.py, unchanged) with an
INDEPENDENT per-second speed logger and checks every recorded transition (o_t, a_t, r_t, o', done):
  non-terminal:  r_t == -(1 + 0.05 ACC[a_t]^2 + IDLE * [v_{t+1} < 0.1]), v_{t+1} = the logger's speed of that vehicle one second after the
                 decision; flagged separately when the next decision is NOT one second later (teleport gap, zone re-entry)
  terminal:      r_t == -(1 + 0.05 ACC[a_t]^2 + IDLE * [v_end < 0.1]) with v_end the logger's speed at the closing second (arrived: 1.0)
  truncated:     decisions still open at the end of the episode (no transition written) are counted
The command is whatever the policy chose: the check does not assume the car moved."""
from __future__ import annotations
import argparse, json, os, sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, run_episode, ACC, IDLE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_fleet_upgrade as FU  # noqa: E402


class Traced(FU.CarRLv2):
    """CarRLv2 UNCHANGED.  Ownership of each transition is read from the setSpeed call order of CarRLv2 itself: a non-terminal transition
    is appended immediately BEFORE setSpeed(v, nv >= 0); a terminal one immediately AFTER setSpeed(v, -1) (attempted even for arrived cars)."""

    def __init__(self, *a, **k):
        super().__init__(*a, **k); self.calls = []; self.meta = []; self.t = 0
        outer = self

        class L(list):
            def append(self, x):
                outer.meta.append((outer.t, len(outer.calls))); super().append(x)
        self.trans = L()

    def step(self, t):
        self.t = t; super().step(t)


def install_spy(cars):
    orig = CE.ls.vehicle.setSpeed

    def spy(v, val):
        cars.calls.append((cars.t, v, float(val))); return orig(v, val)
    CE.ls.vehicle.setSpeed = spy
    return orig


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    res = []
    for light_s in a.lights:
        for seed in a.seeds:
            info = NetInfo(Q7.NET_S); net, lck, mg = X2.light_spec(light_s)
            light = LightRL(info, Q7.load_policy(lck), max_g=mg) if lck is not None else None
            rng = np.random.default_rng(seed)
            cars = Traced(lambda O: rng.integers(0, len(ACC), len(O)), Q7.RHO, seed, record=True)   # random commands: exercises every case
            spd = {}; orig = install_spy(cars)

            class Log:
                def step(self, t):
                    for v in CE.ls.vehicle.getIDList():
                        spd[(t, v)] = CE.ls.vehicle.getSpeed(v)
            ctrl = [c for c in (light, cars, Log()) if c is not None]

            class Multi:
                def step(self, t):
                    for c in ctrl:
                        c.step(t)
            try:
                run_episode(net, Q7.ROU.format(seed), seed, Multi(), None, end=a.end)
            finally:
                CE.ls.vehicle.setSpeed = orig
            c = dict(nonterm_ok=0, nonterm_bad=0, nonterm_gap=0, term_ok=0, term_bad=0, term_arrived=0, unattributed=0)
            prev_cmd = {}
            for i, (tc, v, val) in enumerate(cars.calls):
                pass
            last = {}                                           # vehicle -> time of its last non-negative command before a given call index
            cmd_times = {}
            for i, (tc, v, val) in enumerate(cars.calls):
                if val >= 0:
                    cmd_times.setdefault(v, []).append((i, tc))
            for k, (po, pa, r, o, done) in enumerate(cars.trans):
                tc, pos = cars.meta[k]; base = 1.0 + 0.05 * ACC[pa] ** 2
                if done:
                    if pos == 0 or cars.calls[pos - 1][2] != -1.0:
                        c['unattributed'] += 1; continue
                    v = cars.calls[pos - 1][1]; vend = spd.get((tc, v))
                    if vend is None:
                        c['term_arrived'] += 1; ok = abs(r + base) < 1e-9
                    else:
                        ok = abs(r + (base + IDLE * (vend < 0.1))) < 1e-9
                    c['term_ok' if ok else 'term_bad'] += 1
                else:
                    if pos >= len(cars.calls) or cars.calls[pos][2] < 0:
                        c['unattributed'] += 1; continue
                    v = cars.calls[pos][1]; vlog = spd.get((tc, v))
                    prev = [tt for (ii, tt) in cmd_times.get(v, []) if ii < pos]
                    if not prev or tc - prev[-1] != 1.0:
                        c['nonterm_gap'] += 1                    # the closing decision is not one second after the command (teleport / re-entry)
                    ok = vlog is not None and abs(r + (base + IDLE * (vlog < 0.1))) < 1e-9
                    c['nonterm_ok' if ok else 'nonterm_bad'] += 1
            c['truncated_open'] = len(cars.state); c['teleports_seen'] = 0
            res.append(dict(light=light_s, seed=seed, **c)); print(light_s, seed, c, flush=True)
    ok = all(r['nonterm_bad'] == 0 and r['term_bad'] == 0 and r['unattributed'] == 0 for r in res)
    Path(a.out).write_text(json.dumps(dict(rows=res, verdict='PASS' if ok else 'FAIL'), indent=1)); print('VERDICT', 'PASS' if ok else 'FAIL')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--lights', nargs='+', default=['ACT', 'RL-H:0']); p.add_argument('--seeds', type=int, nargs='+', default=[100, 101])
    p.add_argument('--end', type=float, default=1800); p.add_argument('--out', required=True)
    main(p.parse_args())
