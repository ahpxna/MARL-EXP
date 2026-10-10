#!/usr/bin/env python3
"""G4 second network, PREPARED (04/10/2026 wake 8): train a shared-parameter keep / advance light (scripts/CITY_lightk.LightRLK, all
greens) on RESCO cologne8 (8 lights, TAPAS demand 07:00-08:00; CC BY-NC-SA, kept in external_assets, not redistributed) with human
traffic — the cologne8 analogue of RL-H.  Q7's DQN (7 -> 64 -> 64 -> 2), gamma 0.9, the Q7 epsilon schedule, 200 gradient steps per
episode.  RESCO ships ONE route file, so episodes differ by SUMO's --seed (driver imperfection, departure speed / lane), not by demand;
TRAIN seeds 0-7, evaluation seeds must be disjoint (100+).  Episode = the scenario hour [25200, 28800].  Run with PYTHONHASHSEED=0."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
from scripts.CITY_lightk import NetInfoK, LightRLK  # noqa: E402

R = ROOT / 'external_assets/RESCO/resco_benchmark/environments/cologne8'; NET = str(R / 'cologne8.net.xml'); ROU = str(R / 'cologne8.rou.xml')
SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); BEGIN, END = 25200, 28800


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fn = out / f'{a.name}.pt'
    if fn.exists():
        print('skip', a.name); return
    info = NetInfoK(NET); D = Q7.DQN(7, 2, 0.9, a.seed); E = a.episodes; log = []; t0 = time.perf_counter()
    for ep in range(E):
        seed = ep % 8; eps = Q7.eps_at(ep, E); L = LightRLK(info, D.policy(eps), record=True)
        m = CE.run_episode(NET, ROU, seed, L, None, end=(BEGIN + 300) if a.smoke else END, extra=('--begin', str(BEGIN)))
        D.add(L.trans); loss = D.train(5 if a.smoke else 200)
        r = float(np.mean([x[2] for x in L.trans])) if L.trans else float('nan')
        log.append(dict(ep=ep, seed=seed, eps=eps, n=len(L.trans), mean_r=r, loss=loss, teleports=m['teleports'], wall=time.perf_counter() - t0))
        print(f'[{time.perf_counter() - t0:.0f}s] {a.name} ep {ep} eps {eps:.2f} trans {len(L.trans)} mean r {r:.3f} tele {m["teleports"]}', flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=D.net, kind='lightk', name=a.name, net_file='cologne8', seed=a.seed, episodes=E, source_sha256=SRC,
                    pythonhashseed=os.environ.get('PYTHONHASHSEED'), smoke=a.smoke), fn)
    print('saved', fn, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--seed', type=int, default=11); p.add_argument('--episodes', type=int, default=120)
    p.add_argument('--name', required=True); p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
