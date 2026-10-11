#!/usr/bin/env python3
"""Midtown light trainer with shared + local (per-light) parts and a gate (PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010, Amendment MT-A5; user
11/10: "cho policy riêng và cho thêm policy cục bộ của mỗi đèn ... cân nhắc input ... policy nào là quan trọng hơn? trọng số cao hơn").
The W19 trainer's loop (CITY_w19_train_light.py: family B2D obs and reward, 120 episodes, training traffic in rotation, epsilon 1 -> 0.05
over the first 60 %, 200 double-DQN steps of batch 256 per episode, Huber loss, grad clip 5, Adam 1e-3, soft target 0.01, replay
200 000, gamma 0.9, last checkpoint) with the Q-network replaced by one of:
  ft   SHARED, warm-started from the grid light RL-H_t<k> (research/city_sim/w19_20261008/lights), all weights trained
  lg   SHARED frozen at the grid weights  +  g(s, i) * LOCAL_i(s)   (gate g = sigmoid(MLP([s, emb_i])), learned by the same RL loss)
  ln   SHARED frozen  +  LOCAL_i(s)                                  (no gate: g = 1)
  lo   LOCAL_i(s) only: one 64-64 network per light, from scratch
LOCAL_i is a per-light 32-unit MLP (lo: 64-64) on the light's own observation; its last layer starts at zero, so lg / ln start EXACTLY
at the transferred grid policy.  The light index i (position in sorted NetInfo ids, 224 two-green Midtown lights under MT-A1) is
appended to the observation as one extra column by DEMO_midtown.py when MT_LIGHT_INDEX=1 (training and evaluation alike), so the
evaluators' load_policy (net(obs).argmax) works unchanged.  Run through DEMO_midtown.py (Midtown net, traffic 10-17, MT_TTT for training).
Usage: DEMO_midtown.py scripts/CITY_mt_train_light_moe.py --arm {ft,lg,ln,lo} --k 59 --out DIR [--episodes 120] [--smoke]"""
from __future__ import annotations
import argparse, copy, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np
import torch
import torch.nn as nn

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w19_obs as W  # noqa: E402  (patches CE.LightRL.obs with the family observation)
from scripts.CITY_env import NetInfo, run_episode  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
import scripts.CITY_w19_train_light as T19  # noqa: E402  (LightT: the family reward through LightRL.step)
from scripts.CITY_mt_moe_net import MoEQ  # noqa: E402

SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); GRID = ROOT / 'research/city_sim/w19_20261008/lights'


class DQNM(Q7.DQN):
    """Q7.DQN (replay, double-DQN Huber step, soft target) with an arbitrary network."""

    def __init__(self, net, din, gamma, seed, cap=200_000):
        super().__init__(din, 2, gamma, seed, cap)
        self.net = net; self.tgt = copy.deepcopy(net)
        self.opt = torch.optim.Adam([p for p in self.net.parameters() if p.requires_grad], 1e-3)

    def train(self, steps, bs=256):                       # Q7.DQN.train, with the target copy limited to trainable tensors' twins
        if self.n < bs:
            return float('nan')
        tot = 0.0; pairs = [(p, pt) for p, pt in zip(self.net.parameters(), self.tgt.parameters()) if p.requires_grad]
        for _ in range(steps):
            j = self.rng.integers(0, self.n, bs); S, A, R, S2, D = (torch.as_tensor(x[j]) for x in (self.S, self.A, self.R, self.S2, self.D))
            with torch.no_grad():
                a2 = self.net(S2).argmax(1, keepdim=True); y = R + self.gamma * (1 - D) * self.tgt(S2).gather(1, a2)[:, 0]
            q = self.net(S).gather(1, A[:, None])[:, 0]; loss = nn.functional.smooth_l1_loss(q, y)
            self.opt.zero_grad(); loss.backward(); nn.utils.clip_grad_norm_([p for p, _ in pairs], 5.0); self.opt.step(); tot += loss.item()
            with torch.no_grad():
                for p, pt in pairs:
                    pt.mul_(0.99).add_(0.01 * p)
        return tot / steps


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    indexed = a.arm in ('lg', 'ln', 'lo')
    if indexed != (os.environ.get('MT_LIGHT_INDEX') == '1'):
        sys.exit(f'arm {a.arm}: MT_LIGHT_INDEX must be {"1" if indexed else "unset"}')
    torch.set_num_threads(1)
    fam = W.fam_of(a.k); assert fam == 'B2D', fam
    W.set_family(fam); ok, rk, div = W.FAMS[fam][1], W.FAMS[fam][2], W.FAMS[fam][3]; T19.LightT.RK, T19.LightT.DIV = rk, div
    seed = W.dqn_seed(a.k); torch.manual_seed(seed)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); name = f'RL-H_t{a.k}'
    if (out / f'{name}.pt').exists():
        print('skip', name); return
    E = a.episodes; end = 300 if a.smoke else 3600; info = NetInfo(Q7.NET_S); L = len(info.tls); din = W.DIM[ok]
    grid = torch.load(GRID / f'{name}.pt', weights_only=False); assert grid['family'] == fam and grid['din'] == din
    if a.arm == 'ft':
        net = copy.deepcopy(grid['net'])
    else:
        net = MoEQ(a.arm, L, din, copy.deepcopy(grid['net']) if a.arm in ('lg', 'ln') else None)
    agent = DQNM(net, din + int(indexed), 0.9, seed); steps = 200
    print(f'MT-A5 arm {a.arm} k{a.k} family {fam} obs {ok} din {din}{"+index" if indexed else ""} lights {L} dqn seed {seed} '
          f'teleport {os.environ.get("MT_TTT", "300")} trainable {sum(p.numel() for p in net.parameters() if p.requires_grad)}', flush=True)
    log = []; t0 = time.perf_counter()
    for ep in range(E):
        s = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; eps = Q7.eps_at(ep, E)
        light = T19.LightT(info, agent.policy(eps), record=True)
        m = run_episode(Q7.NET_S, Q7.ROU.format(s), s, light, None, end=end); trans = light.trans
        agent.add(trans); loss = agent.train(steps if not a.smoke else 5)
        r = float(np.mean([x[2] for x in trans])) if trans else float('nan')
        gm = net.gate_mean(torch.as_tensor(np.stack([x[0] for x in trans[-2000:]]))) if (a.arm == 'lg' and trans) else None
        log.append(dict(ep=ep, seed=s, eps=eps, n=len(trans), mean_r=r, loss=loss, teleports=m['teleports'], gate=gm, wall=time.perf_counter() - t0))
        print(f'[{time.perf_counter() - t0:.0f}s] {a.arm} k{a.k} ep {ep} eps {eps:.2f} trans {len(trans)} mean r {r:.4f} loss {loss:.5f}'
              + (f' gate {gm:.3f}' if gm is not None else ''), flush=True)
        (out / f'{name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=net, kind='light', name=name, t=a.k, family=fam, obs=ok, reward=f'-{rk}/{div}', din=din, indexed=indexed, arm=a.arm,
                    lights=sorted(info.tls), dqn_seed=seed, source_sha256=SRC, init=str(GRID / f'{name}.pt'), episodes=E, smoke=a.smoke,
                    teleport=os.environ.get('MT_TTT', '300')), out / f'{name}.pt')
    print(f'saved {out / (name + ".pt")}', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--arm', required=True, choices=['ft', 'lg', 'ln', 'lo']); p.add_argument('--k', type=int, required=True)
    p.add_argument('--out', required=True); p.add_argument('--episodes', type=int, default=120); p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
