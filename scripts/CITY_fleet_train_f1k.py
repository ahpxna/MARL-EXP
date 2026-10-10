#!/usr/bin/env python3
"""F1k trainer (PROTOCOL_CITY_M4_ARTERIAL_20261004 Amendment M4-A7; derived from CITY_fleet_train_f1.py, which is unchanged): the F1 recipe on
the SPIDER network (CITY_m4s_run patches) with the light LightRLK(<--light-ckpt>) (multi-green, frozen) and the provider
CITY_spat_forecast_k (all-branch convention-corrected, multi-green) at quantile Q of TABLE.  Everything else is the F1 trainer verbatim.
Original F1 docstring: the v11 PPO recipe (CITY_fleet_train_v11_ppo.py, frozen, not edited; identical
update rule, hyper-parameters, credit and logging) with TWO declared changes:
  * the light is the ORIGINAL learned light RL-H:k (CE.LightRL with its checkpoint; frozen, never trained), instead of the FT program;
  * the fleet's SPaT is the LOCKED provider: CITY_spat_forecast_c (convention-corrected) at quantile Q of TABLE.
--init PATH fine-tunes from a v11 fleet checkpoint (F1);  --init scratch starts from the zero-init residual V9.NetR(seed) (F1-scratch).
Saves <name>_fleet.pt in the v11 format (usable as PL:<path>).  Run with PYTHONHASHSEED=0, OMP_NUM_THREADS=1."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_m4s_run  # noqa: E402,F401  (spider patches)
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_lightk import NetInfoK, LightRLK  # noqa: E402
import scripts.CITY_spat_forecast_k as FK  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_xplay2 as X2  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_fleet_v9 as V9  # noqa: E402
import scripts.CITY_fleet_v11 as V11  # noqa: E402
import scripts.CITY_es_glosa as ES  # noqa: E402
import scripts.CITY_glosa_lane as GL  # noqa: E402
import scripts.CITY_glosa_lane_d as LD  # noqa: E402
import scripts.CITY_spat_forecast_c as FCC  # noqa: E402
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
SRC = sha(__file__)


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fin = out / f'{a.name}_fleet.pt'
    if fin.exists():
        print('skip', a.name); return
    table = json.loads(Path(a.table).read_text()); spat_fn, _F = FK.make_spat_k(table, a.q)
    for m in (V8, ES, GL, LD, V11):
        m.spat = spat_fn
    lck = a.light_ckpt; lpol = Q7.load_policy(lck); info = NetInfoK(Q7.NET_S)
    if a.init == 'scratch':
        net = V9.NetR(a.seed); init_sha = 'scratch'
    else:
        net = torch.load(a.init, weights_only=False)['net']; init_sha = sha(a.init)
    net.train(); opt = torch.optim.Adam(net.parameters(), lr=3e-4); rng = np.random.default_rng(a.seed); torch.manual_seed(a.seed); log = []
    end = 300 if a.smoke else 3600; t0 = time.perf_counter()
    for ep in range(a.episodes):
        seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; te = time.perf_counter()
        cars = V11.CarPPOL(net, Q7.RHO, seed, deterministic=False, record=True); light = LightRLK(info, lpol)
        m = CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, light, cars, end=end); cars.finish(); tsim = time.perf_counter() - te
        batch = V8.gae(cars.segments, net)
        pl, vl, rdev = V8.ppo_update(net, opt, batch, rng=rng) if batch is not None else (float('nan'),) * 3
        segs = [s for s in cars.segments if s['dec']]; trip_ret = [sum(d['rew'] for d in s['dec']) for s in segs]; st = cars.stats
        row = dict(ep=ep, seed=seed, decisions=st['decisions'], segments=len(segs), teleports=m['teleports'], popped=st['popped'],
                   seg_return_mean=float(np.mean(trip_ret)) if trip_ret else float('nan'),
                   mean_r=float(np.mean([d['rew'] for s in segs for d in s['dec']])) if segs else float('nan'),
                   pi_loss=float(pl), v_loss=float(vl), ratio_dev=float(rdev), log_std=float(net.log_std.item()), t_sim=tsim, wall=time.perf_counter() - t0)
        log.append(row)
        print(f"[{row['wall']:.0f}s] {a.name} ep {ep} seed {seed} dec {row['decisions']} segRet {row['seg_return_mean']:.2f} meanR {row['mean_r']:.3f} "
              f"vloss {row['v_loss']:.3f} std {np.exp(row['log_std']):.3f} tele {row['teleports']} sim {tsim:.1f}s", flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=net, kind='ppo_residual_glosaL', spat='on', reward='AD_tail', name=a.name, seed=a.seed, episodes=a.episodes, light=f'RLK:{a.light_ckpt}', network='spider',
                    light_sha256=sha(lck), init=a.init, init_sha256=init_sha, provider=a.table, provider_sha256=sha(a.table), q=a.q, corrected=True,
                    source_sha256=SRC, v11_sha256=sha(V11.__file__), pythonhashseed=os.environ.get('PYTHONHASHSEED'), smoke=a.smoke), fin)
    print('saved', fin, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--seed', type=int, required=True); p.add_argument('--light-ckpt', required=True); p.add_argument('--init', required=True)
    p.add_argument('--table', required=True); p.add_argument('--q', type=float, required=True); p.add_argument('--episodes', type=int, required=True)
    p.add_argument('--name', required=True); p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
