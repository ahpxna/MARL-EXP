#!/usr/bin/env python3
"""PPO eco-driving pilot trainer v8 (PROTOCOL_CITY_SPAT_PILOT_20261004 Amendments R1 / R2; a pilot INSPIRED by Jayawardana & Wu 2022,
not a reproduction).  Light FT (grid4 static programs, SPaT exact by trace check C-38 / C-38b), training traffic 0-7 in rotation,
3600 s episodes, agents = _stable_u(seed, vid) < 0.5.  Reward B (Eq. 9-10, Table III; L/s fuel; per light-phase interval; fleet-based
over all vehicles; credited to each agent's last decision on that light in the interval).  The two arms differ ONLY in --spat.
PPO (fixed): one rollout = one episode; epochs 4; minibatch 4096; clip 0.2; GAE gamma 0.99 lambda 0.95 per vehicle segment; value
coef 0.5; entropy 0; Adam 3e-4; grad-norm clip 0.5; advantages normalised per batch; rewards x 0.1 for learning.  The LAST
checkpoint is the result (no selection by training statistics).  Resumable: --resume reloads <name>_ckpt.pt (net, optimiser, episode,
rng state, log).  Run with PYTHONHASHSEED=0, OMP_NUM_THREADS=1."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); V8SRC = hashlib.sha256(Path(V8.__file__).read_bytes()).hexdigest()


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fin = out / f'{a.name}_fleet.pt'; ck = out / f'{a.name}_ckpt.pt'
    if fin.exists():
        print('skip', a.name); return
    net = V8.Net(a.seed); opt = torch.optim.Adam(net.parameters(), lr=3e-4); rng = np.random.default_rng(a.seed); log = []; ep0 = 0
    if a.resume and ck.exists():
        c = torch.load(ck, weights_only=False); net.load_state_dict(c['net']); opt.load_state_dict(c['opt']); ep0 = c['ep']; log = c['log']
        rng.bit_generator.state = c['rng']; torch.set_rng_state(c['torch_rng']); print('resumed at episode', ep0, flush=True)
    end = 300 if a.smoke else 3600; t0 = time.perf_counter(); spat_on = a.spat == 'on'
    for ep in range(ep0, a.episodes):
        seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; te = time.perf_counter()
        cars = V8.CarPPO(net, Q7.RHO, seed, spat_on, deterministic=False, record=True, reward='B')
        m = CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, None, cars, end=end); cars.finish(); tsim = time.perf_counter() - te
        batch = V8.gae(cars.segments, net)
        pl, vl, rdev = V8.ppo_update(net, opt, batch, rng=rng) if batch is not None else (float('nan'),) * 3
        segs = [s for s in cars.segments if s['dec']]; trip_ret = [sum(d['rew'] for d in s['dec']) for s in segs]
        L = cars.tracker.log if cars.tracker else []; st = cars.stats
        row = dict(ep=ep, seed=seed, decisions=st['decisions'], segments=len(segs), terminal_exit=st['terminal_exit'], terminal_arrival=st['terminal_arrival'],
                   gap=st['gap'], popped=st['popped'], popped_with_reward=st.get('popped_with_reward', 0), exc=st['exc'], invalid=st['invalid'],
                   teleport_hidden=st['teleport_hidden'], teleports=m['teleports'], spat_valid_share=(st['spat_valid'] / max(1, st['spat_n'])) if spat_on else None,
                   intervals=len(L), branch={b: st['b_' + b] for b in ('R1', 'R2', 'R3', 'R4')}, b_empty=st['b_empty'], capped=st['capped'],
                   phase_reward_mean=float(np.mean([x[7] for x in L])) if L else float('nan'), seg_return_mean=float(np.mean(trip_ret)) if trip_ret else float('nan'),
                   mean_r=float(np.mean([d['rew'] for s in segs for d in s['dec']])) if segs else float('nan'),
                   pi_loss=float(pl), v_loss=float(vl), ratio_dev=float(rdev), log_std=float(net.log_std.item()), t_sim=tsim, wall=time.perf_counter() - t0)
        log.append(row)
        print(f"[{row['wall']:.0f}s] {a.name} ep {ep} seed {seed} dec {row['decisions']} segs {row['segments']} R1-4 {list(row['branch'].values())} "
              f"phaseR {row['phase_reward_mean']:.2f} segRet {row['seg_return_mean']:.2f} vloss {row['v_loss']:.3f} std {np.exp(row['log_std']):.3f} "
              f"gap {row['gap']} exc {row['exc']} tele {row['teleports']} sim {tsim:.1f}s", flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
        if (ep + 1) % 25 == 0 or ep + 1 == a.episodes:
            torch.save(dict(net=net.state_dict(), opt=opt.state_dict(), ep=ep + 1, log=log, rng=rng.bit_generator.state, torch_rng=torch.get_rng_state()), ck)
    torch.save(dict(net=net, kind='ppo', spat=a.spat, reward='B', name=a.name, seed=a.seed, episodes=a.episodes, light='FT', source_sha256=SRC,
                    v8_sha256=V8SRC, pythonhashseed=os.environ.get('PYTHONHASHSEED'), smoke=a.smoke), fin)
    print('saved', fin, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--spat', required=True, choices=['on', 'off']); p.add_argument('--seed', type=int, required=True)
    p.add_argument('--episodes', type=int, required=True); p.add_argument('--name', required=True); p.add_argument('--out', required=True)
    p.add_argument('--smoke', action='store_true'); p.add_argument('--resume', action='store_true')
    main(p.parse_args())
