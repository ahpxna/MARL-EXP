#!/usr/bin/env python3
"""Fleet trainer VERSION 6 (04/10/2026 06:2x, wake 4): CITY_fleet_train_v5 with SANITIZED physical readings.  Found by the training
logs of job 039: two `residual` runs had episodes with POSITIVE mean reward (+11.9, +55.1, +8.0), impossible for a nonnegative cost.  A
negative or sentinel reading (libsumo INVALID_DOUBLE_VALUE = -1073741824) entered the v3 cost; the v3 trace still PASSED because it
compares the reward with the same reading (bookkeeping, not physical validity).  Here every reading is checked:
  speed, allowed speed, fuel rate, acceleration must be finite and > INVALID / 2, with speed >= 0 and allowed > 0; otherwise the reading
  is INVALID: cost 0 by the published API-failure convention, COUNTED per episode (`invalid`, with the minimum raw value seen);
  a finite NEGATIVE fuel rate (an emission-model artifact under hard deceleration) is clamped to 0, the delay term kept, COUNTED (`clamped`);
  an agent MID-TELEPORT (lane '' or a sentinel speed) is skipped for that second: no observation, no decision, no transition; its open
  transition closes when it reappears (the published gap convention), COUNTED (`skipped_teleport_steps`).  Rewards: v3 (delay rate + 0.5 fuel/1000), cotv (CoTV Eq. 2 as a cost).
Actions: acc / release / residual / fine (the v4 classes).  Run with PYTHONHASHSEED=0."""
from __future__ import annotations
import argparse, hashlib, json, math, os, sys, time
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

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); INVALID = -1073741824.0; A_STAR = 3.0
STATS = dict(invalid=0, clamped=0, calls=0, min_raw=0.0, skipped=0)


def ok(x, nonneg=True):
    return math.isfinite(x) and x > INVALID / 2 and (x >= 0 or not nonneg)


def v3_cost_safe(v):
    ls = CE.ls; STATS['calls'] += 1
    try:
        sp = ls.vehicle.getSpeed(v); vm = ls.vehicle.getAllowedSpeed(v); fu = ls.vehicle.getFuelConsumption(v)
    except Exception:
        return 0.0
    if not (ok(sp) and ok(vm) and vm > 0 and ok(fu, nonneg=False)):
        STATS['invalid'] += 1; STATS['min_raw'] = min(STATS['min_raw'], sp, vm, fu); return 0.0
    if fu < 0:                                                  # a finite negative fuel rate (emission-model artifact): clamp, keep the delay
        STATS['clamped'] += 1; STATS['min_raw'] = min(STATS['min_raw'], fu); fu = 0.0
    return max(0.0, 1.0 - sp / vm) + V3.KAPPA * fu / 1000.0


def cotv_cost_safe(v):
    ls = CE.ls; STATS['calls'] += 1
    try:
        e = ls.vehicle.getRoadID(v); ids = ls.edge.getLastStepVehicleIDs(e); vstar = ls.lane.getMaxSpeed(ls.vehicle.getLaneID(v))
    except Exception:
        return 0.0
    if not ids or not (ok(vstar) and vstar > 0):
        return 0.0
    dev = 0.0; acc = 0.0
    for j in ids:
        sj = ls.vehicle.getSpeed(j); aj = ls.vehicle.getAcceleration(j)
        if not (ok(sj) and ok(aj, nonneg=False)):
            STATS['invalid'] += 1; STATS['min_raw'] = min(STATS['min_raw'], sj, aj); return 0.0
        dev += max(0.0, vstar - sj) / (vstar * len(ids)); acc += (max(0.0, aj) / A_STAR) ** 2
    return dev + float(np.sqrt(acc)) / len(ids)


class CarRLv6(V4.CarRLv4):
    def __init__(self, policy, rho, seed, actions, reward, record=False):
        super().__init__(policy, rho, seed, actions, record); self.cost = cotv_cost_safe if reward == 'cotv' else v3_cost_safe

    def step(self, t):
        orig = V3.phys_cost; V3.phys_cost = self.cost
        hidden = set()                                              # agents mid-teleport: no decision, no transition this second
        for v in list(self.agents):
            try:
                if CE.ls.vehicle.getLaneID(v) == '' or not ok(CE.ls.vehicle.getSpeed(v)):
                    hidden.add(v)
            except Exception:
                pass
        STATS['skipped'] = STATS.get('skipped', 0) + len(hidden); self.agents -= hidden
        try:
            super().step(t)
        finally:
            V3.phys_cost = orig; self.agents |= {v for v in hidden if v not in set(CE.ls.simulation.getArrivedIDList())}

    def _end(self, v, arrived=False):
        orig = V3.phys_cost; V3.phys_cost = self.cost
        try:
            super()._end(v, arrived)
        finally:
            V3.phys_cost = orig


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
        seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; eps = Q7.eps_at(ep, E); STATS.update(invalid=0, clamped=0, calls=0, min_raw=0.0, skipped=0)
        light = LightRL(info, lpol, max_g=mg) if lpol is not None else None
        cars = CarRLv6(D.policy(eps), Q7.RHO, seed, a.actions, a.reward, record=True)
        m = run_episode(net, Q7.ROU.format(seed), seed, light, cars, end=end)
        D.add(cars.trans); loss = D.train(steps)
        rr = [x[2] for x in cars.trans]; r = float(np.mean(rr)) if rr else float('nan')
        if rr and max(rr) > 1e-12:
            raise SystemExit(f'positive reward {max(rr)} in episode {ep}: a cost reading escaped the sanitizer')
        log.append(dict(ep=ep, seed=seed, eps=eps, n=len(rr), mean_r=r, loss=loss, released=cars.released / max(1, cars.decided), teleports=m['teleports'],
                        invalid=STATS['invalid'], clamped=STATS['clamped'], skipped_teleport_steps=STATS['skipped'], cost_calls=STATS['calls'], min_raw=STATS['min_raw']))
        print(f'[{time.perf_counter() - t0:.0f}s] {a.name} ep {ep} eps {eps:.2f} mean r {r:.3f} invalid {STATS["invalid"]} clamped {STATS["clamped"]} released {log[-1]["released"]:.2f} tele {m["teleports"]}', flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=D.net, kind='fleet', actions=a.actions, tmax=[1e9, 1e9], name=a.name, against=a.against, reward=a.reward, gamma=a.gamma,
                    fleet_seed=a.fleet_seed, episodes=E, source_sha256=SRC, sanitized=True, pythonhashseed=os.environ.get('PYTHONHASHSEED'), smoke=a.smoke), fn)
    print('saved', fn, 'invalid readings total', sum(r['invalid'] for r in log), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--reward', required=True, choices=['v3', 'cotv']); p.add_argument('--actions', default='acc', choices=['acc', 'release', 'residual', 'fine'])
    p.add_argument('--episodes', type=int, default=120); p.add_argument('--gamma', type=float, default=0.97); p.add_argument('--against', default='ACT')
    p.add_argument('--fleet-seed', type=int, required=True); p.add_argument('--name', required=True); p.add_argument('--out', required=True)
    p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
