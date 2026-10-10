#!/usr/bin/env python3
"""B6 diagnostic, PREPARED ONLY (user audit Addendum B6 item 6; 04/10/2026 wake 4): does the fleet's policy class contain the baseline it
must beat?  The Q7 action set (ACC: -3..+2 m/s^2 every second) has no way to drive like SUMO's default driver model.  Two classes that do:
  --actions release   ACC plus action 6 = release this second to SUMO's driver model (setSpeed(v, -1))
  --actions residual  delta in {-3, -2, -1, 0, +1} added to SUMO's own next speed (vehicle.getSpeedWithoutTraCI); delta = 0 is close to
                      (not identical with) SUMO's choice, because commanding that speed still overrides the model for this step
Reward v3 (scripts/CITY_fleet_train_v3.py: realized (1 - v'/v_allowed) + 0.5 fuel'/1000, same conventions, counted by the v3 trace).
Run only if B6 is negative after the validity checks; it is a known recipe (explicit fallback / residual policy), not a novelty."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, run_episode, ACC, ZONE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_fleet_train_v3 as V3  # noqa: E402

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); DELTA = np.array([-3.0, -2.0, -1.0, 0.0, 1.0])
FINE = np.array([-1.5, -1.0, -0.5, 0.0, 0.5, 1.0]); NACT = {'release': len(ACC) + 1, 'residual': len(DELTA), 'fine': len(FINE)}


class CarRLv4(V3.CarRLv3):
    def __init__(self, policy, rho, seed, actions, record=False):
        super().__init__(policy, rho, seed, record); self.actions = actions; self.released = 0; self.decided = 0

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
                po, pa, _, _ = prev; self.trans.append((po, pa, -V3.phys_cost(v), o, 0.0))
            try:
                vmax = ls.vehicle.getAllowedSpeed(v); self.decided += 1
                if self.actions == 'release' and a == len(ACC):
                    ls.vehicle.setSpeed(v, -1); self.released += 1
                elif self.actions == 'residual':
                    ls.vehicle.setSpeed(v, float(min(max(ls.vehicle.getSpeedWithoutTraCI(v) + DELTA[a], 0.0), vmax)))
                elif self.actions == 'fine':
                    ls.vehicle.setSpeed(v, float(min(max(sp + FINE[a], 0.0), vmax)))
                else:
                    ls.vehicle.setSpeed(v, float(min(max(sp + ACC[a], 0.0), vmax)))
            except Exception:
                continue
            self.state[v] = (o, int(a), 0.0, tid); self.oos_log.append((o[2], o[4] * 60.0))


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fn = out / f'{a.name}_fleet.pt'
    if fn.exists():
        print('skip', a.name); return
    E = a.episodes; end = 300 if a.smoke else 3600; info = NetInfo(Q7.NET_S); net, lck, mg = X2.light_spec(a.against)
    lpol = Q7.load_policy(lck) if lck is not None else None; D = Q7.DQN(6, NACT[a.actions], 0.97, a.fleet_seed)
    log = []; t0 = time.perf_counter(); steps = 5 if a.smoke else 400
    for ep in range(E):
        seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; eps = Q7.eps_at(ep, E)
        light = LightRL(info, lpol, max_g=mg) if lpol is not None else None
        cars = CarRLv4(D.policy(eps), Q7.RHO, seed, a.actions, record=True)
        m = run_episode(net, Q7.ROU.format(seed), seed, light, cars, end=end)
        D.add(cars.trans); loss = D.train(steps)
        r = float(np.mean([x[2] for x in cars.trans])) if cars.trans else float('nan')
        log.append(dict(ep=ep, seed=seed, eps=eps, n=len(cars.trans), mean_r=r, loss=loss, released=cars.released / max(1, cars.decided),
                        teleports=m['teleports'], wall=time.perf_counter() - t0))
        print(f'[{time.perf_counter() - t0:.0f}s] {a.name} ep {ep} eps {eps:.2f} mean r {r:.3f} released {log[-1]["released"]:.2f} tele {m["teleports"]}', flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=D.net, kind='fleet', actions=a.actions, tmax=[1e9, 1e9], name=a.name, against=a.against, reward='v3', kappa=V3.KAPPA,
                    fleet_seed=a.fleet_seed, episodes=E, source_sha256=SRC, pythonhashseed=os.environ.get('PYTHONHASHSEED'), smoke=a.smoke), fn)
    print('saved', fn, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actions', required=True, choices=['release', 'residual', 'fine']); p.add_argument('--against', default='ACT')
    p.add_argument('--episodes', type=int, default=120); p.add_argument('--fleet-seed', type=int, required=True)
    p.add_argument('--name', required=True); p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
