#!/usr/bin/env python3
"""B4F fleet-side support gate (research/city_sim/PROTOCOL_CITY_FLEET_GATE_20261004.md; 04/10/2026 wake 2).  CITY_xplay2's evaluation
with the agent cars wrapped by a gate on the fleet's OWN published support (tmax[green] / tmax[red] of the checkpoint):
  --gate fallback   tau > lim: the car is released to SUMO's driver model for that second (setSpeed(-1)), no action
  --gate clip       tau > lim: the policy acts on the observation with tau replaced by lim
CarRLGate.step is CarRL.step (scripts/CITY_env.py) with only the gate added; when the gate never fires it issues the same calls in the
same order, so under ACT (inside the support by construction) the run is bit-identical to the plain fleet (SELF-CHECK G-0).
Run with PYTHONHASHSEED=0."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, tempfile, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, CarRL, run_episode, ACC, ZONE, IDLE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); CRAWL = 2.0


class CarRLGate(CarRL):
    def __init__(self, policy, rho, seed, tm, mode, record=False):
        super().__init__(policy, rho, seed, record); self.tm, self.mode = tm, mode; self.fired = 0; self.decisions = 0

    def step(self, t):
        ls = CE.ls
        for v in ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                self.agents.add(v); ls.vehicle.setColor(v, (210, 168, 255, 255))
        for v in ls.simulation.getArrivedIDList():
            if v in self.agents:
                self._end(v); self.agents.discard(v)
        ids, O, meta, rel = [], [], [], []
        for v in list(self.agents):
            try:
                nt = ls.vehicle.getNextTLS(v)
                if not nt:
                    self._end(v); continue
                tid, _li, dist, st = nt[0]
                if dist > ZONE:
                    self._end(v); continue
                prev = self.state.get(v)
                if prev is not None and prev[3] != tid:
                    self._end(v); prev = None
                sp = ls.vehicle.getSpeed(v); lead = ls.vehicle.getLeader(v, 100.0)
            except Exception:
                continue
            gap = (lead[1] / 100.0) if lead else 1.0
            o = np.array([dist / ZONE, sp / 14.0, st in 'Gg', st in 'yY', ls.trafficlight.getSpentDuration(tid) / 60.0, gap], np.float32)
            self.decisions += 1; lim = self.tm[1] if o[2] > 0.5 else self.tm[0]
            if o[4] * 60.0 > lim:
                self.fired += 1
                if self.mode == 'fallback':
                    rel.append((v, o, tid, sp)); continue
                o = o.copy(); o[4] = np.float32(lim / 60.0)
            ids.append(v); O.append(o); meta.append((tid, sp))
        for v, o, tid, sp in rel:                               # released to SUMO's driver model for this second
            prev = self.state.get(v)
            if self.record and prev is not None:
                po, pa, pc, _ = prev; self.trans.append((po, pa, -pc, o, 0.0))
            try:
                ls.vehicle.setSpeed(v, -1)
            except Exception:
                continue
            self.state[v] = (o, -1, 1.0 + IDLE * (sp < 0.1), tid); self.oos_log.append((o[2], o[4] * 60.0))
        if not ids:
            return
        A = np.asarray(self.policy(np.stack(O)))
        for v, o, (tid, sp), a in zip(ids, O, meta, A):
            prev = self.state.get(v)
            if self.record and prev is not None:
                po, pa, pc, _ = prev; self.trans.append((po, pa, -pc, o, 0.0))
            try:
                vmax = ls.vehicle.getAllowedSpeed(v); nv = float(min(max(sp + ACC[a], 0.0), vmax)); ls.vehicle.setSpeed(v, nv)
            except Exception:
                continue
            cost = 1.0 + 0.05 * ACC[a] ** 2 + IDLE * (nv < 0.1)
            self.state[v] = (o, int(a), cost, tid); self.oos_log.append((o[2], o[4] * 60.0))


def run(a, seed, end):
    import sumolib
    ls = CE.ls; info = NetInfo(Q7.NET_S); net, lck, mg = X2.light_spec(a.light); fck = X2.fleet_ckpt(a.fleet)
    light = LightRL(info, Q7.load_policy(lck), max_g=mg) if lck is not None else None
    d = torch.load(fck, weights_only=False); tm = d.get('tmax_late') or d['tmax']
    cars = CarRLGate(Q7.load_policy(fck), Q7.RHO, seed, tm, a.gate, record=True)
    cnt = dict(halt_a=0, crawl_a=0, move_a=0, halt_h=0, crawl_h=0, move_h=0)

    class Logger:
        def step(self, t):
            if int(t) % CE.DT_L:
                return
            for tid, dd in info.tls.items():
                for s in dd['serve']:
                    for l in s:
                        for v in ls.lane.getLastStepVehicleIDs(l):
                            sp = ls.vehicle.getSpeed(v); k = 'halt' if sp < 0.1 else ('crawl' if sp < CRAWL else 'move')
                            cnt[f"{k}_{'a' if cars.is_agent(v) else 'h'}"] += 1
    ctrl = [c for c in (light, cars, Logger()) if c is not None]

    class Multi:
        def step(self, t):
            for c in ctrl:
                c.step(t)
    fd, ti = tempfile.mkstemp(suffix='.xml', prefix='xgate_', dir=os.environ.get('XPLAY_TMP')); os.close(fd)
    m = run_episode(net, Q7.ROU.format(seed), seed, Multi(), None, end=end, tripinfo=str(ti))
    trips = [(x.id, float(x.timeLoss), float(x.arrival) >= 0) for x in sumolib.xml.parse(str(ti), 'tripinfo')]
    tl = [x[1] for x in trips]; tla = [x[1] for x in trips if cars.is_agent(x[0])]; tlh = [x[1] for x in trips if not cars.is_agent(x[0])]
    row = dict(light=a.light, fleet=a.fleet, gate=a.gate, sense='default', seed=seed, timeloss=float(np.mean(tl)), n=len(tl),
               timeloss_agent=float(np.mean(tla)), timeloss_human=float(np.mean(tlh)), finished=int(sum(x[2] for x in trips)),
               unfinished=int(sum(not x[2] for x in trips)), teleports=m['teleports'], gate_fired=cars.fired, decisions=cars.decisions, **cnt)
    for g in ('a', 'h'):
        row[f'hidden_{g}'] = cnt[f'crawl_{g}'] / max(1, cnt[f'crawl_{g}'] + cnt[f'halt_{g}'])
    tr = cars.trans; done = sum(x[4] for x in tr); row['approach_cost'] = float(-sum(x[2] for x in tr) / max(1, done))
    lg = np.array(cars.oos_log) if cars.oos_log else np.zeros((0, 2))
    row['tau_oos_mass'] = float(np.mean(lg[:, 1] > np.where(lg[:, 0] > 0.5, tm[1], tm[0]))) if len(lg) else float('nan')
    os.remove(ti)
    return row


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); tag = f'{a.light}_{a.fleet}_{a.gate}'.replace(':', '')
    fn = out / f'{tag}.json'
    if fn.exists() and json.loads(fn.read_text()).get('status') == 'COMPLETE':
        print('skip', tag); return
    rows = []; t0 = time.perf_counter(); end = 600 if a.smoke else 5400
    for s in (a.seeds[:1] if a.smoke else a.seeds):
        r = run(a, s, end); rows.append(r)
        print(f"[{time.perf_counter() - t0:.0f}s] {tag} s{s}: TL {r['timeloss']:.2f} (agent {r['timeloss_agent']:.2f} human {r['timeloss_human']:.2f}) "
              f"cost {r['approach_cost']:.3f} gated {r['gate_fired']}/{r['decisions']} tele {r['teleports']}", flush=True)
    fn.write_text(json.dumps(dict(status='COMPLETE', rows=rows, args=vars(a), source_sha256=SRC, xplay2_sha256=X2.SRC, pythonhashseed=os.environ.get('PYTHONHASHSEED'),
                                  env_sha256=hashlib.sha256((ROOT / 'scripts/CITY_env.py').read_bytes()).hexdigest()), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--light', required=True); p.add_argument('--fleet', required=True); p.add_argument('--gate', required=True, choices=['fallback', 'clip'])
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--out', required=True)
    main(p.parse_args())
