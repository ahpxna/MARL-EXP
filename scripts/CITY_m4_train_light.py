#!/usr/bin/env python3
"""M4 stage 1 (PROTOCOL_CITY_M4_ARTERIAL_20261004): train the shared-parameter keep / advance light (CITY_lightk.LightRLK, all greens) on RESCO
arterial4x4 with all-SUMO traffic.  Q7 DQN (7 -> 64 -> 64 -> 2), gamma 0.9, the Q7 epsilon schedule, 200 updates per episode, halting reward
(LightRLK's).  TRAIN route files arterial4x4_1..8 in rotation (SUMO seed = file index), 3600 s.  Derived from CITY_g4_train_light.py (not edited).
Usage: CITY_m4_train_light.py --seed 11 --episodes 120 --name RLK_a11 --out DIR [--smoke]"""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
from scripts.CITY_lightk import NetInfoK, LightRLK  # noqa: E402
NET = str(ROOT / 'external_assets/RESCO/resco_benchmark/environments/arterial4x4/arterial4x4.net.xml')
VAR = ROOT / 'external_assets/RESCO_variants_20261004/arterial4x4'; ROU = str(VAR / 'arterial4x4_{}.rou.xml'); TRAIN = list(range(1, 9))
SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1); out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fn = out / f'{a.name}.pt'
    if fn.exists():
        print('skip', a.name); return
    info = NetInfoK(NET); D = Q7.DQN(7, 2, 0.9, a.seed); E = a.episodes; log = []; t0 = time.perf_counter()
    for ep in range(E):
        fidx = TRAIN[ep % len(TRAIN)]; eps = Q7.eps_at(ep, E); L = LightRLK(info, D.policy(eps), record=True)
        m = CE.run_episode(NET, ROU.format(fidx), fidx, L, None, end=300 if a.smoke else 3600)
        D.add(L.trans); loss = D.train(5 if a.smoke else 200); r = float(np.mean([x[2] for x in L.trans])) if L.trans else float('nan')
        log.append(dict(ep=ep, file=fidx, eps=eps, n=len(L.trans), mean_r=r, loss=loss, teleports=m['teleports'], wall=time.perf_counter() - t0))
        print(f'[{time.perf_counter() - t0:.0f}s] {a.name} ep {ep} file {fidx} eps {eps:.2f} trans {len(L.trans)} mean r {r:.3f} tele {m["teleports"]}', flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=D.net, kind='lightk', name=a.name, net_file='arterial4x4', seed=a.seed, episodes=E, source_sha256=SRC,
                    pythonhashseed=os.environ.get('PYTHONHASHSEED'), smoke=a.smoke), fn)
    print('saved', fn, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--seed', type=int, default=11); p.add_argument('--episodes', type=int, default=120)
    p.add_argument('--name', required=True); p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true'); main(p.parse_args())
