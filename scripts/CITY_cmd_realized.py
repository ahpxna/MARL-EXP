#!/usr/bin/env python3
"""V1 / H0 (research/papers/audits/TWO_POPULATION_NEW_DIRECTION_VERIFY_20261004.md §V1; 04/10/2026 wake 2): commanded vs realized speed.
CarRL's stage cost uses the COMMANDED speed nv (scripts/CITY_env.py:137-140: IDLE * (nv < 0.1)); SUMO may realize a lower speed (red
light, leader, max decel/accel).  This wrapper is CarRL.step unchanged (same calls, same order, so the trajectory is the plain one) plus
a read-only log: for every agent decision, the commanded nv and the speed SUMO realized one step later.  Per run:
  idle_avoided   decisions with nv >= 0.1 but realized < 0.1 (penalty avoided by command while the car stood), split red / yellow / green
  stopped_accel  decisions taken while stopped (sp < 0.1) that command a > 0
  cost_cmd / cost_real  the approach cost with the commanded vs the realized idle indicator and acceleration
Run with PYTHONHASHSEED=0."""
from __future__ import annotations
import argparse, json, os, sys, tempfile
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, CarRL, run_episode, ACC, IDLE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402


class CarRLLog(CarRL):
    def __init__(self, *a, **k):
        super().__init__(*a, **k); self.pending = {}; self.rec = []

    def step(self, t):
        ls = CE.ls
        for v, (nv, a, sp, st) in self.pending.items():            # realized speed one step after the command
            try:
                vr = ls.vehicle.getSpeed(v)
            except Exception:
                continue
            self.rec.append((nv, vr, a, sp, st))
        self.pending = {}
        n0 = len(self.state)
        before = {v: s for v, s in self.state.items()}
        super().step(t)
        for v, s in self.state.items():                              # decisions taken in this call: state rewritten this step
            if before.get(v) is not s and s[1] >= 0:
                o = s[0]; st = 'G' if o[2] > 0.5 else ('y' if o[3] > 0.5 else 'r'); sp = float(o[1]) * 14.0
                self.pending[v] = (min(max(sp + ACC[s[1]], 0.0), 99.0), s[1], sp, st)


def run(light_s, fleet_s, seed, end):
    import sumolib
    info = NetInfo(Q7.NET_S); net, lck, mg = X2.light_spec(light_s); fck = X2.fleet_ckpt(fleet_s)
    light = LightRL(info, Q7.load_policy(lck), max_g=mg) if lck is not None else None
    cars = CarRLLog(Q7.load_policy(fck), Q7.RHO, seed, record=True)
    ctrl = [c for c in (light, cars) if c is not None]

    class Multi:
        def step(self, t):
            for c in ctrl:
                c.step(t)
    fd, ti = tempfile.mkstemp(suffix='.xml', dir=os.environ.get('XPLAY_TMP')); os.close(fd)
    run_episode(net, Q7.ROU.format(seed), seed, Multi(), None, end=end, tripinfo=ti)
    tl = float(np.mean([float(x.timeLoss) for x in sumolib.xml.parse(ti, 'tripinfo')])); os.remove(ti)
    R = cars.rec; nv = np.array([r[0] for r in R]); vr = np.array([r[1] for r in R]); a = np.array([r[2] for r in R]); sp = np.array([r[3] for r in R])
    st = np.array([r[4] for r in R]); acc = ACC[a]
    ia = (nv >= 0.1) & (vr < 0.1); cost_cmd = 1 + 0.05 * acc ** 2 + IDLE * (nv < 0.1); cost_real = 1 + 0.05 * (vr - sp) ** 2 + IDLE * (vr < 0.1)
    out = dict(light=light_s, fleet=fleet_s, seed=seed, timeloss=tl, decisions=len(R), idle_avoided=float(ia.mean()),
               idle_avoided_of_real_idle=float(ia.sum() / max(1, (vr < 0.1).sum())),
               by_state={s: dict(n=int((st == s).sum()), idle_avoided=float(ia[st == s].mean()) if (st == s).any() else None,
                                 real_idle=float((vr[st == s] < 0.1).mean()) if (st == s).any() else None) for s in 'ryG'},
               stopped_accel=float(((sp < 0.1) & (acc > 0)).sum() / max(1, (sp < 0.1).sum())),
               cmd_vs_real_gap_mean=float(np.mean(nv - vr)), cost_cmd=float(cost_cmd.sum()), cost_real=float(cost_real.sum()),
               idle_cmd=float((nv < 0.1).mean()), idle_real=float((vr < 0.1).mean()))
    return out


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); rows = []
    for L, F in [x.split('/') for x in a.configs]:
        for s in a.seeds:
            r = run(L, F, s, 5400); rows.append(r)
            print(f"{L} x {F} s{s}: TL {r['timeloss']:.2f} decisions {r['decisions']} idle cmd {r['idle_cmd']:.3f} real {r['idle_real']:.3f} "
                  f"avoided-by-command {r['idle_avoided']:.3f} (of real idle {r['idle_avoided_of_real_idle']:.3f}) red {r['by_state']['r']} "
                  f"stopped->accel {r['stopped_accel']:.3f} cost cmd/real {r['cost_cmd']:.0f}/{r['cost_real']:.0f}", flush=True)
            (out / 'rows.json').write_text(json.dumps(rows, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--configs', nargs='+', required=True, help='LIGHT/FLEET'); p.add_argument('--seeds', type=int, nargs='+', default=[100, 101])
    p.add_argument('--out', required=True)
    main(p.parse_args())
