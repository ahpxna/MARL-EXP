#!/usr/bin/env python3
"""M4 generic light trainer (PROTOCOL_CITY_M4_ARTERIAL_20261004, M4-A2 / A3): CITY_lightk.LightRLK (keep / advance over all greens) on any net
with all-SUMO traffic; Q7 DQN (7 -> 64 -> 64 -> 2), gamma 0.9, Q7 epsilon schedule, 200 updates per episode, halting reward; TRAIN seeds 0-7
in rotation (route file = rou pattern with the seed), 3600 s.  Derived from CITY_g4_train_light.py / CITY_m4_train_light.py (not edited)."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
from scripts.CITY_lightk import NetInfoK, LightRLK  # noqa: E402
SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1); out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fn = out / f'{a.name}.pt'
    if fn.exists():
        print('skip', a.name); return
    info = NetInfoK(a.net); D = Q7.DQN(7, 2, 0.9, a.seed); E = a.episodes; log = []; t0 = time.perf_counter()
    for ep in range(E):
        s = ep % 8; eps = Q7.eps_at(ep, E); L = LightRLK(info, D.policy(eps), record=True)
        m = CE.run_episode(a.net, a.rou.format(s), s, L, None, end=300 if a.smoke else 3600)
        D.add(L.trans); loss = D.train(5 if a.smoke else 200); r = float(np.mean([x[2] for x in L.trans])) if L.trans else float('nan')
        log.append(dict(ep=ep, seed=s, eps=eps, n=len(L.trans), mean_r=r, loss=loss, teleports=m['teleports'], wall=time.perf_counter() - t0))
        print(f'[{time.perf_counter() - t0:.0f}s] {a.name} ep {ep} seed {s} eps {eps:.2f} trans {len(L.trans)} mean r {r:.3f} tele {m["teleports"]}', flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=D.net, kind='lightk', name=a.name, net_file=a.net, rou=a.rou, seed=a.seed, episodes=E, source_sha256=SRC,
                    pythonhashseed=os.environ.get('PYTHONHASHSEED'), smoke=a.smoke), fn)
    print('saved', fn, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--net', required=True); p.add_argument('--rou', required=True); p.add_argument('--seed', type=int, default=11)
    p.add_argument('--episodes', type=int, default=120); p.add_argument('--name', required=True); p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
