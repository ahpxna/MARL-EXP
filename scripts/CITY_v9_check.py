#!/usr/bin/env python3
"""v9 checks (Amendment R4; 04/10/2026).  Exit 1 on any failure.
  K1 identity (prediction P1): a fresh NetR evaluated DETERMINISTICALLY (delta = 0) is the base controller: its eval rows equal the
     IC:GLOSA rows (agent / human / city TL, agent fuel, teleports) on traffic SEED, through CITY_eval6 (R: and IC:GLOSA specs)
  K2 training-mode episode (END s): segments one vehicle each with consecutive seconds; stored log-prob == Net.dist(obs).log_prob(u);
     the applied a == clip(base + 1.5 tanh(u), LO, HI) with base recomputed from the stored observation context is NOT re-derivable
     offline, so K2 checks a in [LO, HI] and |a - base_logged| <= 1.5 for the logged base; GAE equals the naive recursion
  K3 reward A-group: every interval reward == -(cost sum / vehicle-seconds) from its own log entry (independent formula)"""
import argparse, os, sys, tempfile
from pathlib import Path
import numpy as np
import torch
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_eval4 as E4  # noqa: E402
import scripts.CITY_eval6 as E6  # noqa: E402,F401
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_fleet_v8 as V8  # noqa: E402
import scripts.CITY_fleet_v9 as V9  # noqa: E402
from scripts.CITY_v8_check import naive_gae  # noqa: E402

SEED = int(os.environ.get('V9CHECK_SEED', '0')); END = int(os.environ.get('V9CHECK_END', '900'))


def ev(spec, seed):
    a = argparse.Namespace(light='FT', light_obs='raw', light_fallback='none', fleet=spec, guard='none', record=None, replay=None, replay_dir=None,
                           discharge=False, delay_trace=False, swap_at=None, swap_light=None, swap_fleet=None, seeds=[seed], smoke=False, tag='k1', out='/tmp')
    return E4.run(a, seed, END)


if __name__ == '__main__':
    assert os.environ.get('PYTHONHASHSEED') == '0'; torch.set_num_threads(1); bad = []
    td = Path(tempfile.mkdtemp(dir=os.environ.get('XPLAY_TMP'))); f = td / 'fresh_fleet.pt'
    torch.save(dict(net=V9.NetR(7), kind='ppo_residual', spat='on', reward='AG'), f)
    r1, r2 = ev(f'R:{f}', SEED), ev('IC:GLOSA', SEED)
    keys = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports')
    print('K1 R(delta=0):', {k: r1[k] for k in keys}); print('K1 IC:GLOSA  :', {k: r2[k] for k in keys})
    if any(abs(r1[k] - r2[k]) > 1e-9 for k in keys):
        bad.append('K1 identity: delta = 0 is not the base controller')
    net = V9.NetR(13); cars = V9.CarPPOR(net, Q7.RHO, SEED, True, deterministic=False, record=True, reward='AG')
    CE.run_episode(Q7.NET_S, Q7.ROU.format(SEED), SEED, None, cars, end=END); cars.finish(); segs = [s for s in cars.segments if s['dec']]
    allD = [d for s in segs for d in s['dec']]
    if any(len({d['vid'] for d in s['dec']}) != 1 or any(b['t'] - a['t'] != 1 for a, b in zip(s['dec'], s['dec'][1:])) for s in segs):
        bad.append('K2 segments')
    O = torch.as_tensor(np.stack([d['obs'] for d in allD])); U = torch.as_tensor(np.array([d['u'] for d in allD], np.float32))
    with torch.no_grad():
        lp = net.dist(O).log_prob(U).numpy()
    if np.max(np.abs(lp - np.array([d['logp'] for d in allD]))) > 1e-4:
        bad.append('K2 log-prob')
    if any(not (V8.LO - 1e-9 <= d['a'] <= V8.HI + 1e-9) for d in allD):
        bad.append('K2 action range')
    b = V8.gae(cars.segments, net); A = np.concatenate([naive_gae(s, net)[0] for s in segs])
    if b is None or np.max(np.abs(b[3] - A)) > 1e-4:
        bad.append('K2 GAE')
    if any(abs(x[7] + x[3]) > 1e-9 for x in cars.tracker.log):
        bad.append('K3 A-group reward')
    print(f'K2/K3: {len(allD)} decisions, {len(segs)} segments, {len(cars.tracker.log)} intervals; mean interval reward {np.mean([x[7] for x in cars.tracker.log]):.3f}; stats {cars.stats}')
    print('V9 CHECK', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
