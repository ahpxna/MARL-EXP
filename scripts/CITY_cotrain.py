#!/usr/bin/env python3
"""B2 / B3 of research/city_sim/PROTOCOL_CITY_COTRAIN_20261004.md (04/10/2026 wake 2): staged fleets and light–car co-training on the
Q7 environment (grid4 static net, rho 0.5, demand seeds 0–7, 3600 s episodes, Q7's DQN and epsilon schedule).  Run with PYTHONHASHSEED=0.
  --mode sim       both populations learn in every episode (independent learners)
  --mode alt       alternating blocks of --block episodes, light first; each population learns --episodes episodes; the frozen one is greedy
  --mode fleet-vs  only the fleet learns, against the frozen light --light-ckpt (B2: L-RLH_t against RL-H_t)
  --reward halt | delay   the light's training reward: -halting/10 (RL-H's) or -sum over served-lane vehicles of (1 - v/v_allowed), /10
Outputs <out>/<name>_light.pt and/or <name>_fleet.pt (Q7 checkpoint format: net, tmax, ...) and <name>.log.json."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, CarRL, run_episode, NA_CAR  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


class LightRLDelay(LightRL):
    """RL-H's controller and observation; the value used as reward is the served lanes' instantaneous time-loss rate."""

    def obs(self, tid):
        o, _halt, cur = super().obs(tid)
        ls = CE.ls; dl = 0.0
        for s in self.info.tls[tid]['serve']:
            for l in s:
                for v in ls.lane.getLastStepVehicleIDs(l):
                    vm = ls.vehicle.getAllowedSpeed(v)
                    dl += max(0.0, 1.0 - ls.vehicle.getSpeed(v) / vm) if vm > 0 else 1.0
        return o, dl, cur


def schedule(a):
    if a.mode == 'sim':
        return [(True, True)] * a.episodes
    if a.mode == 'fleet-vs':
        return [(False, True)] * a.episodes
    s = []
    for b in range(2 * a.episodes // a.block):
        s += [(b % 2 == 0, b % 2 == 1)] * a.block
    return s


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0 (set-order jitter, xplay Addendum A1)')
    torch.set_num_threads(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); E = a.episodes; end = 300 if a.smoke else 3600; info = NetInfo(Q7.NET_S)
    done = [out / f'{a.name}_{p}.pt' for p in (('fleet',) if a.mode == 'fleet-vs' else ('light', 'fleet'))]
    if all(p.exists() for p in done):
        print('skip', a.name); return
    Ld = None if a.mode == 'fleet-vs' else Q7.DQN(7, 2, 0.9, a.light_seed)
    Fd = Q7.DQN(6, NA_CAR, 0.97, a.fleet_seed)
    frozen = Q7.load_policy(a.light_ckpt) if a.mode == 'fleet-vs' else None
    LC = LightRLDelay if a.reward == 'delay' else LightRL
    nL = nF = 0; tmax = [0.0, 0.0]; tmax_late = [0.0, 0.0]; log = []; t0 = time.perf_counter(); steps = (5, 5) if a.smoke else (200, 400)
    for ep, (lL, lF) in enumerate(schedule(a)):
        seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]
        if frozen is not None:
            light = LightRL(info, frozen)
        else:
            light = LC(info, Ld.policy(Q7.eps_at(nL, E) if lL else 0.0), record=lL)
        cars = CarRL(Fd.policy(Q7.eps_at(nF, E) if lF else 0.0), Q7.RHO, seed, record=lF)
        m = run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, light, cars, end=end)
        row = dict(ep=ep, seed=seed, learn_light=lL, learn_fleet=lF, teleports=m['teleports'])
        if lL:
            Ld.add(light.trans); row.update(eps_L=Q7.eps_at(nL, E), n_L=len(light.trans), r_L=float(np.mean([x[2] for x in light.trans])) if light.trans else float('nan'),
                                            loss_L=Ld.train(steps[0])); nL += 1
        if lF:
            Fd.add(cars.trans); row.update(eps_F=Q7.eps_at(nF, E), n_F=len(cars.trans), r_F=float(np.mean([x[2] for x in cars.trans])) if cars.trans else float('nan'),
                                           loss_F=Fd.train(steps[1])); nF += 1
            for g, tau in cars.oos_log:
                tmax[int(g)] = max(tmax[int(g)], tau)
                if nF > 0.8 * E:                              # the last 20 % of the fleet's learning episodes (the light it ends up facing)
                    tmax_late[int(g)] = max(tmax_late[int(g)], tau)
        row['wall'] = time.perf_counter() - t0; log.append(row)
        print(f"[{row['wall']:.0f}s] {a.name} ep {ep} L {'learn' if lL else 'frozen'} r {row.get('r_L', float('nan')):.3f} "
              f"F {'learn' if lF else 'frozen'} r {row.get('r_F', float('nan')):.3f} tele {m['teleports']}", flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    meta = dict(name=a.name, mode=a.mode, reward=a.reward, light_seed=a.light_seed, fleet_seed=a.fleet_seed, light_ckpt=a.light_ckpt,
                episodes=E, block=a.block, source_sha256=SRC, env_sha256=hashlib.sha256((ROOT / 'scripts/CITY_env.py').read_bytes()).hexdigest(),
                pythonhashseed=os.environ.get('PYTHONHASHSEED'), smoke=a.smoke, learned_L=nL, learned_F=nF)
    if Ld is not None:
        torch.save(dict(net=Ld.net, kind='light', tmax=None, **meta), out / f'{a.name}_light.pt')
    torch.save(dict(net=Fd.net, kind='fleet', tmax=tmax, tmax_late=tmax_late, **meta), out / f'{a.name}_fleet.pt')
    print(f'saved {a.name} (light episodes {nL}, fleet episodes {nF}) tmax {tmax} late {tmax_late}', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--mode', required=True, choices=['sim', 'alt', 'fleet-vs']); p.add_argument('--reward', default='halt', choices=['halt', 'delay'])
    p.add_argument('--name', required=True); p.add_argument('--out', required=True); p.add_argument('--episodes', type=int, default=120)
    p.add_argument('--block', type=int, default=20); p.add_argument('--light-seed', type=int, default=1011); p.add_argument('--fleet-seed', type=int, default=1013)
    p.add_argument('--light-ckpt'); p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
