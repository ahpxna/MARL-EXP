#!/usr/bin/env python3
"""L4 green-release guard (research/city_sim/PROTOCOL_CITY_GREEN_GUARD_20261004.md; 04/10/2026 wake 3).  CITY_xplay_gate's evaluation
with a different release rule for the frozen fleet:
  --guard green       the agent car is released to SUMO's driver model whenever its head shows GREEN (it keeps its policy on red / yellow)
  --guard green+oos   as green, and also released when tau exceeds the fleet's published support (the B4F fallback) on red / yellow
Unlike the B4F gate, the guard is NOT a no-op under the training light (ACT greens are in support); its cost under ACT is measured.
Metrics add fuel (SUMO emissions device, mg per trip) and realized stops.  Run with PYTHONHASHSEED=0."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, tempfile, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, run_episode, read_tripinfo  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_xplay_gate as XG  # noqa: E402

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


class CarRLGuard(XG.CarRLGate):
    """CarRLGate.step with the release test widened: green always releases; 'green+oos' also releases out-of-support red/yellow."""

    def __init__(self, policy, rho, seed, tm, guard, record=False):
        super().__init__(policy, rho, seed, tm, 'fallback', record); self.guard = guard
        if guard == 'none':
            self.tm = [float('inf'), float('inf')]                # never fires: the plain fleet (same calls as CarRL), for fuel / stops
        elif guard == 'green':
            self.tm = [float('inf'), float('-inf')]               # red never fires on tau; green always fires (tau >= 0 > -inf)
        else:
            self.tm = [tm[0], float('-inf')]


def run(a, seed, end):
    info = NetInfo(Q7.NET_S); net, lck, mg = X2.light_spec(a.light); fck = X2.fleet_ckpt(a.fleet)
    light = LightRL(info, Q7.load_policy(lck), max_g=mg) if lck is not None else None
    d = torch.load(fck, weights_only=False); tm = d.get('tmax_late') or d['tmax']
    cars = CarRLGuard(Q7.load_policy(fck), Q7.RHO, seed, tm, a.guard, record=True)
    ctrl = [c for c in (light, cars) if c is not None]

    class Multi:
        def step(self, t):
            for c in ctrl:
                c.step(t)
    fd, ti = tempfile.mkstemp(suffix='.xml', prefix='xguard_', dir=os.environ.get('XPLAY_TMP')); os.close(fd)
    m = run_episode(net, Q7.ROU.format(seed), seed, Multi(), None, end=end, tripinfo=str(ti))
    rows = read_tripinfo(ti, agents=None); os.remove(ti)
    ag = [r for r in rows if cars.is_agent(r['id'])]; hu = [r for r in rows if not cars.is_agent(r['id'])]
    mean = lambda xs, k: float(np.mean([x[k] for x in xs])) if xs else float('nan')
    return dict(light=a.light, fleet=a.fleet, guard=a.guard, seed=seed, timeloss=mean(rows, 'timeloss'), timeloss_agent=mean(ag, 'timeloss'),
                timeloss_human=mean(hu, 'timeloss'), fuel_agent=mean(ag, 'fuel'), fuel_human=mean(hu, 'fuel'), fuel=mean(rows, 'fuel'),
                waiting_agent=mean(ag, 'waiting'), n=len(rows), unfinished=int(sum(not r['finished'] for r in rows)), teleports=m['teleports'],
                released=cars.fired, decisions=cars.decisions)


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); tag = f'{a.light}_{a.fleet}_{a.guard}'.replace(':', '').replace('+', 'P')
    fn = out / f'{tag}.json'
    if fn.exists() and json.loads(fn.read_text()).get('status') == 'COMPLETE':
        print('skip', tag); return
    rows = []; t0 = time.perf_counter()
    for s in a.seeds:
        r = run(a, s, 5400); rows.append(r)
        print(f"[{time.perf_counter() - t0:.0f}s] {tag} s{s}: TL {r['timeloss']:.2f} (agent {r['timeloss_agent']:.2f} human {r['timeloss_human']:.2f}) "
              f"fuel agent {r['fuel_agent']:.0f} released {r['released']}/{r['decisions']} tele {r['teleports']}", flush=True)
    fn.write_text(json.dumps(dict(status='COMPLETE', rows=rows, args=vars(a), source_sha256=SRC, gate_sha256=XG.SRC, pythonhashseed=os.environ.get('PYTHONHASHSEED')), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--light', required=True); p.add_argument('--fleet', required=True); p.add_argument('--guard', required=True, choices=['green', 'green+oos', 'none'])
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--out', required=True)
    main(p.parse_args())
