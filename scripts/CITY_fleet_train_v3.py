#!/usr/bin/env python3
"""B6 (research/city_sim/PROTOCOL_CITY_B6_BENEFICIAL_FLEET_20261004.md; 04/10/2026 wake 3): train a fleet with a PHYSICAL objective, because
the fleet-benefit audit (city ledger C-17) found every Q7/Q7b fleet worse than human driving on time and fuel, even under its training light.
Reward v3, charged when the transition closes (the car's next decision one second later, or the end of its approach), on REALIZED
quantities only:  cost = (1 - v'/v_allowed) + KAPPA * fuel'(mg/s) / 1000, with v' and fuel' read from SUMO at closing time.  The first term
is the per-second time-loss rate (what tripinfo's timeLoss integrates); the second is the instantaneous fuel rate (emissions device on).
Training otherwise as scripts/CITY_fleet_upgrade.py (mode new / ft; any frozen light).  Run with PYTHONHASHSEED=0."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, CarRL, run_episode, NA_CAR, ACC, ZONE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); KAPPA = 0.5


def phys_cost(v):
    ls = CE.ls
    try:
        sp = ls.vehicle.getSpeed(v); vm = ls.vehicle.getAllowedSpeed(v); fu = ls.vehicle.getFuelConsumption(v)
    except Exception:
        return 0.0
    delay = max(0.0, 1.0 - sp / vm) if vm > 0 else 1.0
    return delay + KAPPA * fu / 1000.0


class CarRLv3(CarRL):
    """CarRL.step; the stage cost of a decision is the physical cost observed one second later (or at the approach end)."""

    def step(self, t):
        ls = CE.ls
        for v in ls.simulation.getDepartedIDList():
            if self.is_agent(v):
                self.agents.add(v); ls.vehicle.setColor(v, (210, 168, 255, 255))
        for v in ls.simulation.getArrivedIDList():
            if v in self.agents:
                self._end(v, arrived=True); self.agents.discard(v)
        ids, O, meta = [], [], []
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
            ids.append(v); O.append(o); meta.append((tid, sp))
        if not ids:
            return
        A = np.asarray(self.policy(np.stack(O)))
        for v, o, (tid, sp), a in zip(ids, O, meta, A):
            prev = self.state.get(v)
            if self.record and prev is not None:
                po, pa, _, _ = prev; self.trans.append((po, pa, -phys_cost(v), o, 0.0))
            try:
                vmax = ls.vehicle.getAllowedSpeed(v); nv = float(min(max(sp + ACC[a], 0.0), vmax)); ls.vehicle.setSpeed(v, nv)
            except Exception:
                continue
            self.state[v] = (o, int(a), 0.0, tid); self.oos_log.append((o[2], o[4] * 60.0))

    def _end(self, v, arrived=False):
        prev = self.state.pop(v, None)
        if prev is not None:
            c = 0.0 if arrived else phys_cost(v)
            try:
                CE.ls.vehicle.setSpeed(v, -1)
            except Exception:
                pass
            if self.record:
                po, pa, _, _ = prev; self.trans.append((po, pa, -c, po, 1.0))


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fn = out / f'{a.name}_fleet.pt'
    if fn.exists():
        print('skip', a.name); return
    E = a.episodes; end = 300 if a.smoke else 3600; info = NetInfo(Q7.NET_S); net, lck, mg = X2.light_spec(a.against)
    lpol = Q7.load_policy(lck) if lck is not None else None; D = Q7.DQN(6, NA_CAR, 0.97, a.fleet_seed)
    tmax = [0.0, 0.0]; tmax_late = [0.0, 0.0]; log = []; t0 = time.perf_counter(); steps = 5 if a.smoke else 400
    for ep in range(E):
        seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; eps = Q7.eps_at(ep, E)
        light = LightRL(info, lpol, max_g=mg) if lpol is not None else None
        cars = CarRLv3(D.policy(eps), Q7.RHO, seed, record=True)
        m = run_episode(net, Q7.ROU.format(seed), seed, light, cars, end=end)
        D.add(cars.trans); loss = D.train(steps)
        for g, tau in cars.oos_log:
            tmax[int(g)] = max(tmax[int(g)], tau)
            if ep >= 0.8 * E:
                tmax_late[int(g)] = max(tmax_late[int(g)], tau)
        r = float(np.mean([x[2] for x in cars.trans])) if cars.trans else float('nan')
        log.append(dict(ep=ep, seed=seed, eps=eps, n=len(cars.trans), mean_r=r, loss=loss, teleports=m['teleports'], wall=time.perf_counter() - t0))
        print(f'[{time.perf_counter() - t0:.0f}s] {a.name} ep {ep} eps {eps:.2f} trans {len(cars.trans)} mean r {r:.3f} loss {loss:.4f} tele {m["teleports"]}', flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=D.net, kind='fleet', tmax=tmax, tmax_late=tmax_late, name=a.name, mode='new', against=a.against, reward='v3', kappa=KAPPA,
                    fleet_seed=a.fleet_seed, episodes=E, source_sha256=SRC, pythonhashseed=os.environ.get('PYTHONHASHSEED'), smoke=a.smoke), fn)
    print(f'saved {fn} tmax {tmax} late {tmax_late}', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--against', required=True); p.add_argument('--episodes', type=int, default=120); p.add_argument('--fleet-seed', type=int, required=True)
    p.add_argument('--name', required=True); p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
