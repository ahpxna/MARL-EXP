#!/usr/bin/env python3
"""W6-4 LCD trainer (PROTOCOL_CITY_WAVE6_20261005): a learned committed-duration light, the DHCP-type structure (predictable; it publishes
exact timing through N8's spat_cdc at evaluation).  At the onset of every yellow the next green's duration is chosen from D by a shared DQN
over f = [n_cur, n_oth, h_cur, h_oth] / 20 (vehicles / halting on the lanes of the green to start and of the other green) and committed; at
the green onset it is applied with setPhaseDuration(max(1, d - spent)) (the CDC mechanism of CITY_eval_n8.py, copied, so the trainer does not
import the evaluator).  The first green at t = 0 is decided at its onset.  Reward of a decision = -(halting vehicle-seconds on all lanes of the
light from this commit to its next commit) / 100; the last open decision of an episode is dropped.  SUMO cars only; TRAIN seeds 0-7 cycled.
DQN: MLP 64-64, replay 200 k, batch 256, Adam 1e-3, Huber, gamma 0.9 per decision, target copied every episode, 300 updates per episode,
eps 1 -> 0.05 linearly over the first 80 episodes.  Usage: CITY_lcd.py --seed j --episodes 120 --out DIR [--smoke]"""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from collections import deque
from pathlib import Path
import numpy as np
import torch
import torch.nn as nn
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402
D_ACT = np.array([5, 10, 15, 20, 25, 30, 40, 50, 60], float); DMIN, DMAX = 5.0, 60.0
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()


def qnet():
    return nn.Sequential(nn.Linear(4, 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, len(D_ACT)))


def feats(info, tid, g):
    ls = CE.ls; d = info.tls[tid]; cur = d['greens'].index(g); oth = 1 - cur
    h = [sum(ls.lane.getLastStepHaltingNumber(l) for l in s) for s in d['serve'][:2]]
    n = [sum(ls.lane.getLastStepVehicleNumber(l) for l in s) for s in d['serve'][:2]]
    return np.array([n[cur], n[oth], h[cur], h[oth]], np.float32) / 20.0


class LCDTrain:
    def __init__(self, info, net, eps, rng):
        self.info, self.net, self.eps, self.rng = info, net, eps, rng; self.ids = list(info.tls); self.last = {}; self.plan = {}
        self.open = {}; self.acc = {t: 0.0 for t in self.ids}; self.trans = []; self.durs = []
        self.lanes = {t: sorted({l for s in info.tls[t]['serve'] for l in s}) for t in self.ids}

    def choose(self, f):
        if self.rng.random() < self.eps:
            return int(self.rng.integers(len(D_ACT)))
        with torch.no_grad():
            return int(self.net(torch.as_tensor(f[None]))[0].argmax())

    def decide(self, tid, g, commit):
        f = feats(self.info, tid, g); a = self.choose(f)
        if commit:
            if tid in self.open:
                f0, a0 = self.open[tid]; self.trans.append((f0, a0, -self.acc[tid] / 100.0, f))
            self.open[tid] = (f, a); self.acc[tid] = 0.0
        return float(D_ACT[a])

    def step(self, t):
        ls = CE.ls
        for tid in self.ids:
            d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid); n_ph = d['n_phases']
            self.acc[tid] += sum(ls.lane.getLastStepHaltingNumber(l) for l in self.lanes[tid])
            if self.last.get(tid) != ph:
                if ph in d['greens']:
                    dur = self.plan.pop(tid, None)
                    if dur is None:
                        dur = self.decide(tid, ph, commit=False)
                    ls.trafficlight.setPhaseDuration(tid, max(1.0, dur - ls.trafficlight.getSpentDuration(tid))); self.durs.append(dur)
                else:
                    nxt = (ph + 1) % n_ph
                    if nxt in d['greens']:
                        self.plan[tid] = self.decide(tid, nxt, commit=True)
            self.last[tid] = ph


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.set_num_threads(1); torch.manual_seed(1000 + a.seed); rng = np.random.default_rng(1000 + a.seed)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fin = out / f'LCD_j{a.seed}.pt'
    if fin.exists():
        print('skip', fin); return
    info = Q7.NetInfo(Q7.NET_S); net = qnet(); tgt = qnet(); tgt.load_state_dict(net.state_dict()); opt = torch.optim.Adam(net.parameters(), 1e-3)
    R = deque(maxlen=200_000); end = 300 if a.smoke else 3600; log = []; t0 = time.perf_counter(); E_EPS = max(1, round(a.episodes * 80 / 120))
    for ep in range(a.episodes):
        eps = max(0.05, 1.0 - (1.0 - 0.05) * ep / E_EPS); seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; te = time.perf_counter()
        L = LCDTrain(info, net, eps, rng); m = CE.run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, L, None, end=end); R.extend(L.trans)
        losses = []
        if len(R) >= 256:
            for _ in range(300):
                ix = rng.integers(0, len(R), 256); f0 = torch.as_tensor(np.stack([R[i][0] for i in ix])); a0 = torch.as_tensor([R[i][1] for i in ix])
                r = torch.as_tensor([R[i][2] for i in ix], dtype=torch.float32); f1 = torch.as_tensor(np.stack([R[i][3] for i in ix]))
                with torch.no_grad():
                    y = r + 0.9 * tgt(f1).max(1).values
                q = net(f0).gather(1, a0[:, None])[:, 0]; loss = nn.functional.smooth_l1_loss(q, y)
                opt.zero_grad(); loss.backward(); opt.step(); losses.append(loss.item())
        tgt.load_state_dict(net.state_dict())
        row = dict(ep=ep, seed=seed, eps=eps, transitions=len(L.trans), replay=len(R), ret=float(np.mean([x[2] for x in L.trans])) if L.trans else float('nan'),
                   dur_mean=float(np.mean(L.durs)) if L.durs else float('nan'), loss=float(np.mean(losses)) if losses else float('nan'), teleports=m['teleports'],
                   t_ep=time.perf_counter() - te, wall=time.perf_counter() - t0)
        log.append(row); (out / f'LCD_j{a.seed}.log.json').write_text(json.dumps(log))
        print(f"[{row['wall']:.0f}s] LCD j{a.seed} ep {ep} seed {seed} eps {eps:.2f} trans {row['transitions']} meanR {row['ret']:.3f} dur {row['dur_mean']:.1f} "
              f"loss {row['loss']:.4f} tele {row['teleports']} t {row['t_ep']:.1f}s", flush=True)
    torch.save(dict(state=net.state_dict(), actions=D_ACT.tolist(), features='[n_cur, n_oth, h_cur, h_oth] / 20', seed=a.seed, episodes=a.episodes, smoke=a.smoke,
                    source_sha256=sha(__file__), pythonhashseed=os.environ.get('PYTHONHASHSEED')), fin)
    print('saved', fin, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--seed', type=int, required=True); p.add_argument('--episodes', type=int, default=120)
    p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true'); main(p.parse_args())
