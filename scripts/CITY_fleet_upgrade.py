#!/usr/bin/env python3
"""F0 / V3 of research/city_sim/PROTOCOL_CITY_FLEET_UPGRADE_20261004.md (04/10/2026 wake 3): train an UPGRADED fleet F1 against a FROZEN
light L0, or a reward-v2 fleet against ACT.  Q7's DQN, environment and demand seeds 0–7 (3600 s), rho 0.5.  Run with PYTHONHASHSEED=0.
  --mode ft    fine-tune from --init (F0's checkpoint): epsilon 0.2 -> 0.05 over 60 % of the episodes, fresh replay buffer
  --mode new   from scratch (Q7 schedule 1.0 -> 0.05)
  --against    a light spec of scripts/CITY_xplay2.light_spec (ACT | FT | RL-H:t | RL-J:t | RL-C50:t | <ARM>:k), frozen and greedy
  --reward v1  CarRL's stage cost: 1 + 0.05 a^2 + IDLE*[COMMANDED nv < 0.1] (scripts/CITY_env.py:140)
  --reward v2  CarRLv2: 1 + 0.05 a^2 + IDLE*[REALIZED speed < 0.1], the realized speed being read at the car's next decision (one second
               later, the next observation's speed) or at the end of its approach (city ledger C-13: v1's idle term is avoided by command)
Output <out>/<name>_fleet.pt in Q7's checkpoint format (net, tmax, tmax_late, meta) and <name>.log.json."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, CarRL, run_episode, NA_CAR, ACC, ZONE, IDLE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


class CarRLv2(CarRL):
    """CarRL.step with the idle indicator on the REALIZED speed.  state[v] holds the base cost 1 + 0.05 a^2; the idle term is added when
    the transition is closed: at the next decision from the new observation's speed (o[1] * 14), at the approach end from the current speed."""

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
                po, pa, base, _ = prev; self.trans.append((po, pa, -(base + IDLE * (sp < 0.1)), o, 0.0))
            try:
                vmax = ls.vehicle.getAllowedSpeed(v); nv = float(min(max(sp + ACC[a], 0.0), vmax)); ls.vehicle.setSpeed(v, nv)
            except Exception:
                continue
            self.state[v] = (o, int(a), 1.0 + 0.05 * ACC[a] ** 2, tid); self.oos_log.append((o[2], o[4] * 60.0))

    def _end(self, v, arrived=False):
        prev = self.state.pop(v, None)
        if prev is not None:
            sp = 1.0
            try:
                if not arrived:
                    sp = CE.ls.vehicle.getSpeed(v)
                CE.ls.vehicle.setSpeed(v, -1)
            except Exception:
                pass
            if self.record:
                po, pa, base, _ = prev; self.trans.append((po, pa, -(base + IDLE * (sp < 0.1)), po, 1.0))


def eps_ft(ep, E):
    return max(0.05, 0.2 - 0.15 * ep / max(1, int(0.6 * E)))


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fn = out / f'{a.name}_fleet.pt'
    if fn.exists():
        print('skip', a.name); return
    E = a.episodes; end = 300 if a.smoke else 3600; info = NetInfo(Q7.NET_S); net, lck, mg = X2.light_spec(a.against)
    lpol = Q7.load_policy(lck) if lck is not None else None
    D = Q7.DQN(6, NA_CAR, 0.97, a.fleet_seed); init_sha = None
    if a.mode == 'ft':
        ck = torch.load(a.init, weights_only=False); D.net.load_state_dict(ck['net'].state_dict()); D.tgt.load_state_dict(ck['net'].state_dict())
        init_sha = hashlib.sha256(Path(a.init).read_bytes()).hexdigest()
    Car = CarRLv2 if a.reward == 'v2' else CarRL
    tmax = [0.0, 0.0]; tmax_late = [0.0, 0.0]; log = []; t0 = time.perf_counter(); steps = 5 if a.smoke else 400
    for ep in range(E):
        seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; eps = eps_ft(ep, E) if a.mode == 'ft' else Q7.eps_at(ep, E)
        light = LightRL(info, lpol, max_g=mg) if lpol is not None else None
        cars = Car(D.policy(eps), Q7.RHO, seed, record=True)
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
    torch.save(dict(net=D.net, kind='fleet', tmax=tmax, tmax_late=tmax_late, name=a.name, mode=a.mode, against=a.against, reward=a.reward,
                    init=a.init, init_sha256=init_sha, fleet_seed=a.fleet_seed, episodes=E, source_sha256=SRC, pythonhashseed=os.environ.get('PYTHONHASHSEED'),
                    env_sha256=hashlib.sha256((ROOT / 'scripts/CITY_env.py').read_bytes()).hexdigest(), smoke=a.smoke), fn)
    print(f'saved {fn} tmax {tmax} late {tmax_late}', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--mode', required=True, choices=['ft', 'new']); p.add_argument('--init'); p.add_argument('--against', required=True)
    p.add_argument('--reward', required=True, choices=['v1', 'v2']); p.add_argument('--episodes', type=int, default=120)
    p.add_argument('--fleet-seed', type=int, required=True); p.add_argument('--name', required=True); p.add_argument('--out', required=True)
    p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
