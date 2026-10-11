#!/usr/bin/env python3
"""B6-R recipe screen, PREPARED ONLY (04/10/2026 wake 4; user step 4 "kiểm recipe/horizon"): train fleets with
  --reward v3     (CITY_fleet_train_v3: realized delay rate + 0.5 fuel/1000 of the agent itself)
  --reward cotv   CoTV's published CAV reward (Guo et al., T-ITS 2023, arXiv 2201.13143 Eq. 2), as a COST on the agent's current edge K:
                  sum_j (v* - v_j)/(v* |K|)  +  sqrt(sum_j (a_j^+ / a*)^2) / |K|,  v* = lane speed limit, a* = 3 m/s^2, a_j^+ = max(a_j, 0)
                  (a cooperative, road-level reward over every vehicle on the agent's edge; realized one second later, like v3)
  --actions acc | release | residual   (the v4 classes)
  --episodes  training budget (CoTV used about 4.5x our 120 x 3600 s in simulated seconds)
Conventions as v3 (API failure -> 0, arrived terminal -> 0, approach-zone horizon).  Run with PYTHONHASHSEED=0."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, run_episode  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_fleet_train_v3 as V3  # noqa: E402
import scripts.CITY_fleet_train_v4 as V4  # noqa: E402

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); A_STAR = 3.0
PREV_SPEED = {}


def cotv_cost(v):
    ls = CE.ls
    try:
        e = ls.vehicle.getRoadID(v); ids = ls.edge.getLastStepVehicleIDs(e)
        vstar = max(ls.lane.getMaxSpeed(ls.vehicle.getLaneID(v)), 1e-6)
    except Exception:
        return 0.0
    if not ids:
        return 0.0
    dev = 0.0; acc = 0.0
    for j in ids:
        sj = ls.vehicle.getSpeed(j); dev += max(0.0, vstar - sj) / (vstar * len(ids))
        aj = max(0.0, ls.vehicle.getAcceleration(j)); acc += (aj / A_STAR) ** 2
    return dev + float(np.sqrt(acc)) / len(ids)


class CarRLv5(V4.CarRLv4):
    def __init__(self, policy, rho, seed, actions, reward, record=False):
        super().__init__(policy, rho, seed, actions, record); self.reward = reward

    def step(self, t):
        if self.reward == 'cotv':
            orig = V3.phys_cost; V3.phys_cost = cotv_cost
            try:
                super().step(t)
            finally:
                V3.phys_cost = orig
        else:
            super().step(t)

    def _end(self, v, arrived=False):
        if self.reward == 'cotv':
            orig = V3.phys_cost; V3.phys_cost = cotv_cost
            try:
                super()._end(v, arrived)
            finally:
                V3.phys_cost = orig
        else:
            super()._end(v, arrived)


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fn = out / f'{a.name}_fleet.pt'
    if fn.exists():
        print('skip', a.name); return
    E = a.episodes; end = 300 if a.smoke else 3600; info = NetInfo(Q7.NET_S); net, lck, mg = X2.light_spec(a.against)
    lpol = Q7.load_policy(lck) if lck is not None else None; nact = {'acc': len(CE.ACC), **V4.NACT}[a.actions]
    D = Q7.DQN(6, nact, a.gamma, a.fleet_seed); log = []; t0 = time.perf_counter(); steps = 5 if a.smoke else 400
    for ep in range(E):
        seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; eps = Q7.eps_at(ep, E)
        light = LightRL(info, lpol, max_g=mg) if lpol is not None else None
        cars = CarRLv5(D.policy(eps), Q7.RHO, seed, 'acc' if a.actions == 'acc' else a.actions, a.reward, record=True)
        m = run_episode(net, Q7.ROU.format(seed), seed, light, cars, end=end)
        D.add(cars.trans); loss = D.train(steps)
        r = float(np.mean([x[2] for x in cars.trans])) if cars.trans else float('nan')
        log.append(dict(ep=ep, seed=seed, eps=eps, n=len(cars.trans), mean_r=r, loss=loss, released=cars.released / max(1, cars.decided), teleports=m['teleports']))
        print(f'[{time.perf_counter() - t0:.0f}s] {a.name} ep {ep} eps {eps:.2f} mean r {r:.3f} released {log[-1]["released"]:.2f} tele {m["teleports"]}', flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=D.net, kind='fleet', actions=a.actions if a.actions != 'acc' else 'acc', tmax=[1e9, 1e9], name=a.name, against=a.against,
                    reward=a.reward, gamma=a.gamma, fleet_seed=a.fleet_seed, episodes=E, source_sha256=SRC, pythonhashseed=os.environ.get('PYTHONHASHSEED'),
                    smoke=a.smoke), fn)
    print('saved', fn, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--reward', required=True, choices=['v3', 'cotv']); p.add_argument('--actions', default='acc', choices=['acc', 'release', 'residual', 'fine'])
    p.add_argument('--episodes', type=int, default=120); p.add_argument('--gamma', type=float, default=0.97); p.add_argument('--against', default='ACT')
    p.add_argument('--fleet-seed', type=int, required=True); p.add_argument('--name', required=True); p.add_argument('--out', required=True)
    p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
