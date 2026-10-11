#!/usr/bin/env python3
"""Fleet trainer VERSION 7 (04/10/2026 wake 8; PROTOCOL_CITY_B6 §B6-H): CITY_fleet_train_v6 (sanitized readings, teleport skipping,
positive-reward abort) plus a HORIZON option.
  --horizon approach (= v6): a car's control episode ends at the stop line.  When its next signal changes, the last transition is
           TERMINAL (done = 1) with the cost read at that moment, and a new episode starts at the next approach.
  --horizon trip: approaches are CHAINED.  When the next signal changes and the car is already inside the next zone, the stored
           transition is carried over (its signal id is rewritten), so the next decision closes it as a NON-terminal transition
           (done = 0) whose next state is the first observation of the new approach.  The episode ends only at arrival (terminal 0,
           as before), when the car has no next signal, or when it is outside every zone.  Counted per episode: `chained`.
Rewards, action sets, sanitizer: unchanged from v6.  Run with PYTHONHASHSEED=0."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, run_episode, ZONE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_fleet_train_v4 as V4  # noqa: E402
import scripts.CITY_fleet_train_v6 as V6  # noqa: E402

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


class CarRLv7(V6.CarRLv6):
    def __init__(self, policy, rho, seed, actions, reward, horizon, record=False):
        super().__init__(policy, rho, seed, actions, reward, record); self.horizon = horizon; self.chained = 0

    def step(self, t):
        if self.horizon == 'trip':
            for v, st in list(self.state.items()):
                try:
                    nt = CE.ls.vehicle.getNextTLS(v)
                except Exception:
                    continue
                if nt and nt[0][0] != st[3] and nt[0][2] <= ZONE:
                    self.state[v] = (st[0], st[1], st[2], nt[0][0]); self.chained += 1
        super().step(t)


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fn = out / f'{a.name}_fleet.pt'
    if fn.exists():
        print('skip', a.name); return
    E = a.episodes; end = 300 if a.smoke else 3600; info = NetInfo(Q7.NET_S); net, lck, mg = X2.light_spec(a.against)
    lpol = Q7.load_policy(lck) if lck is not None else None; nact = {'acc': len(CE.ACC), **V4.NACT}[a.actions]
    D = Q7.DQN(6, nact, a.gamma, a.fleet_seed); log = []; t0 = time.perf_counter(); steps = 5 if a.smoke else 400; S = V6.STATS
    for ep in range(E):
        seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; eps = Q7.eps_at(ep, E); S.update(invalid=0, clamped=0, calls=0, min_raw=0.0, skipped=0)
        light = LightRL(info, lpol, max_g=mg) if lpol is not None else None
        cars = CarRLv7(D.policy(eps), Q7.RHO, seed, a.actions, a.reward, a.horizon, record=True)
        m = run_episode(net, Q7.ROU.format(seed), seed, light, cars, end=end)
        D.add(cars.trans); loss = D.train(steps)
        rr = [x[2] for x in cars.trans]; r = float(np.mean(rr)) if rr else float('nan')
        if rr and max(rr) > 1e-12:
            raise SystemExit(f'positive reward {max(rr)} in episode {ep}: a cost reading escaped the sanitizer')
        nterm = int(sum(x[4] for x in cars.trans))
        log.append(dict(ep=ep, seed=seed, eps=eps, n=len(rr), terminal=nterm, chained=cars.chained, mean_r=r, loss=loss,
                        released=cars.released / max(1, cars.decided), teleports=m['teleports'], invalid=S['invalid'], clamped=S['clamped'],
                        skipped_teleport_steps=S['skipped'], cost_calls=S['calls'], min_raw=S['min_raw']))
        print(f'[{time.perf_counter() - t0:.0f}s] {a.name} ep {ep} eps {eps:.2f} mean r {r:.3f} trans {len(rr)} terminal {nterm} chained {cars.chained} '
              f'invalid {S["invalid"]} released {log[-1]["released"]:.2f} tele {m["teleports"]}', flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=D.net, kind='fleet', actions=a.actions, tmax=[1e9, 1e9], name=a.name, against=a.against, reward=a.reward, gamma=a.gamma,
                    horizon=a.horizon, fleet_seed=a.fleet_seed, episodes=E, source_sha256=SRC, sanitized=True,
                    pythonhashseed=os.environ.get('PYTHONHASHSEED'), smoke=a.smoke), fn)
    print('saved', fn, 'invalid readings total', sum(r['invalid'] for r in log), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--reward', required=True, choices=['v3', 'cotv']); p.add_argument('--actions', default='acc', choices=['acc', 'release', 'residual', 'fine'])
    p.add_argument('--horizon', required=True, choices=['approach', 'trip'])
    p.add_argument('--episodes', type=int, default=120); p.add_argument('--gamma', type=float, default=0.97); p.add_argument('--against', default='ACT')
    p.add_argument('--fleet-seed', type=int, required=True); p.add_argument('--name', required=True); p.add_argument('--out', required=True)
    p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
