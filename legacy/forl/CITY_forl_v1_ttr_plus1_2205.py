#!/usr/bin/env python3
"""W11 FoRL port (PROTOCOL_CITY_WAVE11_FORL_20261005 + Amendment A1): Forecasting-conditioned RL (Gerner, Bogenberger, Schmidtner, XAI@IJCAI
2026; external_assets/FORL_26_IJCAIXAI @ c7acfc56) ported to the grid4 keep / switch signal shared by the 16 controllers.
  * action: L = 5 keep / switch values per decision (MultiDiscrete); only the first is executed (wrappers.PredictionWrapper.step);
  * reward conditioning (wrappers._get_prediction_reward, direct_penalty): the forecast made index+1 decisions earlier, at position index+1,
    vs the executed action; a mismatch adds KAPPA * BETA ** index to this decision's reward;
  * loss conditioning: LAMBDA x cross-entropy of heads 1..L-1 vs the actions executed 1..L-1 decisions later (ppo_with_forecastloss);
    the authors' tls default is LAMBDA = 0;
  * observation: RL-H's 7 inputs + the controller's previous forecast (L - 1 entries; add_predictions_to_state);
  * PPO (SB3 defaults of forl/config.yaml): separate pi / vf MLPs 256-256 tanh, orthogonal init, gamma 0.99, GAE 0.95, clip 0.2, 10 epochs,
    minibatch 256, Adam 3e-4, entropy 0, value coefficient 0.5, per-minibatch advantage normalisation; one update per 3600-s episode.
Environment as RL-H: decisions every DT_L s outside yellows after MIN_G, reward -(halting on incoming lanes)/10 at the controller's next
decision, SUMO drivers only, TRAIN 0-7 in rotation.
Usage: CITY_forl.py --seed s --episodes 200 --name FORL_s<s> --out DIR [--smoke]"""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from collections import deque
from pathlib import Path
import numpy as np
import torch
import torch.nn as nn
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, run_episode, DT_L, MIN_G, YELLOW  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402

L, KAPPA, BETA, LAMBDA = 5, -0.25, 0.95, 0.0
GAMMA, GAE, CLIP, EPOCHS, MB, LR, VF, ENT = 0.99, 0.95, 0.2, 10, 256, 3e-4, 0.5, 0.0
OBS = 7 + (L - 1)
SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


class Net(nn.Module):
    def __init__(self):
        super().__init__()
        self.pi = nn.Sequential(nn.Linear(OBS, 256), nn.Tanh(), nn.Linear(256, 256), nn.Tanh(), nn.Linear(256, 2 * L))
        self.vf = nn.Sequential(nn.Linear(OBS, 256), nn.Tanh(), nn.Linear(256, 256), nn.Tanh(), nn.Linear(256, 1))
        for seq, gain in ((self.pi, 0.01), (self.vf, 1.0)):              # SB3: hidden sqrt(2), policy head 0.01, value head 1
            for i, m in enumerate(seq):
                if isinstance(m, nn.Linear):
                    nn.init.orthogonal_(m.weight, gain=(gain if i == len(seq) - 1 else 2 ** 0.5)); nn.init.zeros_(m.bias)

    def dist(self, x):
        return torch.distributions.Categorical(logits=self.pi(x).view(-1, L, 2))

    def value(self, x):
        return self.vf(x).squeeze(-1)


def base_obs(info, tid):
    ls = CE.ls; d = info.tls[tid]; ph = ls.trafficlight.getPhase(tid)
    h = [sum(ls.lane.getLastStepHaltingNumber(x) for x in s) for s in d['serve']]
    n = [sum(ls.lane.getLastStepVehicleNumber(x) for x in s) for s in d['serve']]
    cur = d['greens'].index(ph) if ph in d['greens'] else -1
    return np.array([h[0] / 10, h[1] / 10, n[0] / 20, n[1] / 20, cur == 0, cur == 1, ls.trafficlight.getSpentDuration(tid) / 60], np.float32), sum(h), cur


class LightFoRL:
    """Shared FoRL policy for every controller.  train=True samples and records PPO data; train=False is argmax per head.  self.fc[tid] =
    (decision time, forecast entries 1..L-1) feeds the SPaT provider."""

    def __init__(self, info, net, train=False, seed=0):
        self.info, self.net, self.train = info, net, train; self.ids = list(info.tls)
        self.prev_fc = {t: np.zeros(L - 1, np.float32) for t in self.ids}; self.old = {t: deque(maxlen=L - 1) for t in self.ids}
        self.fc = {}; self.traj = {t: [] for t in self.ids}; self.gen = torch.Generator().manual_seed(seed); self.dec = 0; self.miss = 0

    def step(self, t):
        if int(t) % DT_L:
            return
        ls = CE.ls; todo, O = [], []
        for tid in self.ids:
            o, halt, cur = base_obs(self.info, tid)
            if cur < 0:
                continue
            if ls.trafficlight.getSpentDuration(tid) < MIN_G:
                ls.trafficlight.setPhaseDuration(tid, 1e5); continue
            if self.train and self.traj[tid] and self.traj[tid][-1]['r_env'] is None:
                self.traj[tid][-1]['r_env'] = -halt / 10
            todo.append((tid, cur)); O.append(np.concatenate([o, self.prev_fc[tid]]))
        if not todo:
            return
        X = torch.as_tensor(np.stack(O))
        with torch.no_grad():
            dist = self.net.dist(X)
            if self.train:
                u = torch.rand(dist.probs.shape[:2], generator=self.gen); A = (u < dist.probs[..., 1]).long()
                logp = dist.log_prob(A).sum(-1); V = self.net.value(X)
            else:
                A = dist.probs.argmax(-1)
        A = A.numpy()
        for j, (tid, cur) in enumerate(todo):
            a = A[j]; rp = 0.0; self.dec += 1
            for index, P in enumerate(self.old[tid]):                   # P = the action vector of index+1 decisions ago
                if P[index + 1] != a[0]:
                    rp += KAPPA * (BETA ** index); self.miss += 1
            self.old[tid].appendleft(a.copy()); self.prev_fc[tid] = a[1:].astype(np.float32); self.fc[tid] = (float(t), a[1:].copy())
            if self.train:
                self.traj[tid].append(dict(o=O[j], a=a.copy(), logp=float(logp[j]), v=float(V[j]), r_pred=rp, r_env=None))
            if a[0] == 1:
                d = self.info.tls[tid]; ls.trafficlight.setPhase(tid, (d['greens'][cur] + 1) % d['n_phases'])
            else:
                ls.trafficlight.setPhaseDuration(tid, 1e5)


def ppo_update(net, opt, light):
    obs, act, logp0, adv, ret = [], [], [], [], []; tgt, tmask = [], []
    for tid, tr in light.traj.items():
        tr = [x for x in tr if x['r_env'] is not None] + ([tr[-1]] if tr and tr[-1]['r_env'] is None else [])
        if len(tr) < 2:
            continue
        boot = tr[-1]['v'] if tr[-1]['r_env'] is None else 0.0; steps = [x for x in tr if x['r_env'] is not None]
        r = np.array([x['r_env'] + x['r_pred'] for x in steps]); v = np.array([x['v'] for x in steps] + [boot]); g = 0.0; A = np.zeros(len(steps))
        for i in range(len(steps) - 1, -1, -1):
            delta = r[i] + GAMMA * v[i + 1] - v[i]; g = delta + GAMMA * GAE * g; A[i] = g
        acts = [x['a'] for x in tr]
        for i, x in enumerate(steps):
            obs.append(x['o']); act.append(x['a']); logp0.append(x['logp']); adv.append(A[i]); ret.append(A[i] + x['v'])
            fut = np.zeros(L - 1, np.int64); m = np.zeros(L - 1, np.float32)
            for k in range(1, L):
                if i + k < len(acts):
                    fut[k - 1] = acts[i + k][0]; m[k - 1] = 1.0
            tgt.append(fut); tmask.append(m)
    if not obs:
        return dict(n=0)
    O = torch.as_tensor(np.stack(obs)); Aa = torch.as_tensor(np.stack(act)); LP = torch.as_tensor(logp0, dtype=torch.float32)
    AD = torch.as_tensor(adv, dtype=torch.float32); RT = torch.as_tensor(ret, dtype=torch.float32)
    TG = torch.as_tensor(np.stack(tgt)); TM = torch.as_tensor(np.stack(tmask)); n = len(O); stats = dict(n=n)
    for _ in range(EPOCHS):
        perm = torch.randperm(n)
        for s in range(0, n, MB):
            idx = perm[s:s + MB]; d = net.dist(O[idx]); lp = d.log_prob(Aa[idx]).sum(-1)
            ad = AD[idx]; ad = (ad - ad.mean()) / (ad.std() + 1e-8) if len(idx) > 1 else ad
            ratio = torch.exp(lp - LP[idx]); pl = -torch.min(ratio * ad, torch.clamp(ratio, 1 - CLIP, 1 + CLIP) * ad).mean()
            vl = ((net.value(O[idx]) - RT[idx]) ** 2).mean(); ent = d.entropy().sum(-1).mean()
            loss = pl + VF * vl - ENT * ent
            if LAMBDA:
                fl = -(d.logits[:, 1:, :].log_softmax(-1).gather(-1, TG[idx].unsqueeze(-1)).squeeze(-1) * TM[idx]).sum() / TM[idx].sum().clamp(min=1)
                loss = loss + LAMBDA * fl
            opt.zero_grad(); loss.backward(); nn.utils.clip_grad_norm_(net.parameters(), 0.5); opt.step()
        stats.update(pl=float(pl), vl=float(vl), ent=float(ent))
    return stats


def train(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    torch.manual_seed(a.seed); np.random.seed(a.seed); torch.set_num_threads(1)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); fn = out / f'{a.name}.pt'
    if fn.exists():
        print('skip', a.name); return
    info = NetInfo(Q7.NET_S); net = Net(); opt = torch.optim.Adam(net.parameters(), lr=LR, eps=1e-5); log = []; t0 = time.perf_counter()
    end = 300 if a.smoke else 3600
    for ep in range(a.episodes):
        seed = Q7.TRAIN_SEEDS[ep % len(Q7.TRAIN_SEEDS)]; light = LightFoRL(info, net, train=True, seed=a.seed * 100003 + ep)
        m = run_episode(Q7.NET_S, Q7.ROU.format(seed), seed, light, None, end=end)
        st = ppo_update(net, opt, light)
        renv = float(np.mean([x['r_env'] for tr in light.traj.values() for x in tr if x['r_env'] is not None] or [np.nan]))
        log.append(dict(ep=ep, seed=seed, decisions=light.dec, forecast_miss=light.miss, mean_r_env=renv, teleports=m['teleports'], wall=time.perf_counter() - t0, **st))
        print(f'[{time.perf_counter() - t0:.0f}s] {a.name} ep {ep} dec {light.dec} miss {light.miss} r_env {renv:.3f} {st}', flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    torch.save(dict(state=net.state_dict(), kind='forl', name=a.name, seed=a.seed, episodes=a.episodes, L=L, kappa=KAPPA, beta=BETA, lam=LAMBDA,
                    source_sha256=SRC, upstream='urbanAIthi/26_FORL_IJCAIXAI@c7acfc56', smoke=a.smoke), fn)
    print('saved', fn, flush=True)


def load(path):
    d = torch.load(path, weights_only=False); net = Net(); net.load_state_dict(d['state']); net.eval(); return net


def make_spat_forl(holder, info):
    """SPaT from the light's own forecast: yellow whose next green serves the link -> exact; current green serving the link -> ttr to the first
    forecast switch; the other green -> that + YELLOW; no switch within the horizon or no decision in this green -> invalid."""
    stc = {}; stats = dict(valid=0, yellow=0, forl=0, invalid=0)
    inval = lambda src: dict(ttg=0.0, ttr=0.0, valid=False, source=src)  # noqa: E731

    def spat(tid, link):
        light = holder.get('light')
        if light is None or tid not in info.tls:
            stats['invalid'] += 1; return inval('unavailable')
        ls = CE.ls; t = float(ls.simulation.getTime())
        if tid not in stc:
            stc[tid] = [p.state for p in ls.trafficlight.getAllProgramLogics(tid)[0].phases]
        st = stc[tid]; d = info.tls[tid]; greens = list(d['greens']); K = len(greens)
        serve = [k for k, g in enumerate(greens) if link < len(st[g]) and st[g][link] in 'Gg']
        if len(serve) == K:
            stats['valid'] += 1; return dict(ttg=0.0, ttr=999.0, valid=True, source='always')
        if not serve:
            stats['invalid'] += 1; return inval('never-green')
        ph = ls.trafficlight.getPhase(tid); tau = float(ls.trafficlight.getSpentDuration(tid))
        if ph not in greens:                                            # yellow after green ci: the next green is fixed
            ci = max([k for k, g in enumerate(greens) if g < ph], default=K - 1); nx = (ci + 1) % K
            if nx in serve:
                stats['valid'] += 1; stats['yellow'] += 1; return dict(ttg=max(0.0, YELLOW - tau) + 1.0, ttr=0.0, valid=True, source='yellow')
            stats['invalid'] += 1; return inval('yellow-other')
        ci = greens.index(ph); fc = light.fc.get(tid)
        if fc is None or fc[0] < t - tau - 1e-9:                        # no decision yet in this green
            stats['invalid'] += 1; return inval('no-decision')
        ks = [i + 1 for i, f in enumerate(fc[1]) if f == 1]
        if not ks:
            stats['invalid'] += 1; return inval('beyond-horizon')
        rem = max(0.0, fc[0] + ks[0] * DT_L - t); stats['valid'] += 1; stats['forl'] += 1
        if ci in serve:
            return dict(ttg=0.0, ttr=rem + 1.0, valid=True, source='forl')
        return dict(ttg=rem + YELLOW + 1.0, ttr=0.0, valid=True, source='forl')
    spat.stats = stats
    return spat


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--seed', type=int, required=True); p.add_argument('--episodes', type=int, default=200)
    p.add_argument('--name', required=True); p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true')
    train(p.parse_args())
