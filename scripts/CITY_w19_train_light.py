#!/usr/bin/env python3
"""W19 light trainer (PROTOCOL_CITY_WAVE19_20261008): CITY_q7b_contract.train for kind 'light' (human traffic, no fleet), line for line,
with the W19 family's observation (scripts/CITY_w19_obs.py) and training reward.  The reward enters through LightRL.step's -halt / 10:
LightT returns halt' = H for reward H / 10 (bit-identical to RL-H), else halt' = 10 * Q / div.
Self-check KW19-0: --fam AH --t 19 reproduces CITY_q7b_contract.py --train-light ... --t 19 bit for bit (compared on --smoke by the job).
Usage: CITY_w19_train_light.py --out DIR --k K [--episodes 120] [--smoke] [--dqn-t T  (seed 11 + 100 T; default by slot)]"""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w19_obs as W  # noqa: E402  (patches CE.LightRL.obs)
from scripts.CITY_env import NetInfo, LightRL, run_episode  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); OBS_SRC = hashlib.sha256(Path(W.__file__).read_bytes()).hexdigest()


class LightT(LightRL):
    RK, DIV = 'H', 10

    def obs(self, tid):
        o, halt, cur = super().obs(tid)
        if self.RK == 'H' and self.DIV == 10:
            return o, halt, cur
        return o, 10.0 * W.reward_quantity(self.info, tid, self.RK) / self.DIV, cur


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1)
    fam = W.fam_of(a.k); assert fam, a.k; W.set_family(fam); _k0, ok, rk, div = W.FAMS[fam]; LightT.RK, LightT.DIV = rk, div
    seed = 11 + 100 * a.dqn_t if a.dqn_t is not None else W.dqn_seed(a.k)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); name = a.name or f'RL-H_t{a.k}'
    if (out / f'{name}.pt').exists():
        print('skip', name); return
    E = a.episodes; end = 300 if a.smoke else 3600; info = NetInfo(Q7.NET_S); log = []; t0 = time.perf_counter()
    agent = Q7.DQN(W.DIM[ok], 2, 0.9, seed); steps = 200
    print(f'W19 train k{a.k} family {fam} obs {ok} dim {W.DIM[ok]} reward -{rk}/{div} dqn seed {seed}', flush=True)
    for ep in range(E):
        s = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; eps = Q7.eps_at(ep, E)
        light = LightT(info, agent.policy(eps), record=True)
        m = run_episode(Q7.NET_S, Q7.ROU.format(s), s, light, None, end=end); trans = light.trans
        agent.add(trans); loss = agent.train(steps if not a.smoke else 5)
        r = float(np.mean([x[2] for x in trans])) if trans else float('nan')
        log.append(dict(ep=ep, seed=s, eps=eps, n=len(trans), mean_r=r, loss=loss, teleports=m['teleports'], wall=time.perf_counter() - t0))
        print(f'[{time.perf_counter() - t0:.0f}s] {name} k{a.k} ep {ep} eps {eps:.2f} trans {len(trans)} mean r {r:.4f} loss {loss:.5f}', flush=True)
        (out / f'{name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=agent.net, kind='light', name=name, t=a.k, family=fam, obs=ok, reward=f'-{rk}/{div}', din=W.DIM[ok], dqn_seed=seed,
                    source_sha256=SRC, obs_sha256=OBS_SRC, episodes=E, smoke=a.smoke), out / f'{name}.pt')
    print(f'saved {out / (name + ".pt")}', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--out', required=True); p.add_argument('--k', type=int, required=True)
    p.add_argument('--episodes', type=int, default=120); p.add_argument('--smoke', action='store_true'); p.add_argument('--dqn-t', type=int)
    p.add_argument('--name'); main(p.parse_args())
