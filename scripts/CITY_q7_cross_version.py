#!/usr/bin/env python3
"""Q7 (research/city_sim/PROTOCOL_CITY_Q7_CROSS_VERSION_20261002.md, written 21:4x EDT 02/10/2026): learned lights × learned
cars in SUMO grid4.  Trains shared-parameter DQNs with scripts/CITY_env.py (LightRL, CarRL) and evaluates the cross-version
matrix.  Modes:
  --train-light NAME [--with-fleet CKPT]       RL-H (human traffic) or RL-J (with a frozen learned fleet at rho 0.5)
  --train-fleet NAME --against ACT|CKPT       L-ACT (against SUMO actuated) or L-RLH (against a frozen RL light)
  --eval                                       the matrix of the protocol on evaluation seeds 100–104, then the report
Usage: CITY_q7_cross_version.py --out DIR <mode> [--episodes 120] [--smoke]"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_env import NetInfo, LightRL, CarRL, run_episode, NA_CAR  # noqa: E402

NET_S = str(ROOT / 'research/city_sim/net/grid4.net.xml'); NET_A = str(ROOT / 'research/city_sim/net/grid4_actuated.net.xml')
ROU = str(ROOT / 'research/city_sim/demand/grid4/rou_s{}.xml'); TRAIN_SEEDS = list(range(8)); EVAL_SEEDS = [100, 101, 102, 103, 104]
RHO, MAXG_COMPAT = 0.5, 50
SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


class DQN:
    def __init__(self, din, nact, gamma, seed, cap=200_000):
        torch.manual_seed(seed); self.rng = np.random.default_rng(seed); self.gamma, self.nact = gamma, nact
        mk = lambda: nn.Sequential(nn.Linear(din, 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, nact))
        self.net, self.tgt = mk(), mk(); self.tgt.load_state_dict(self.net.state_dict()); self.opt = torch.optim.Adam(self.net.parameters(), 1e-3)
        self.S = np.zeros((cap, din), np.float32); self.A = np.zeros(cap, np.int64); self.R = np.zeros(cap, np.float32)
        self.S2 = np.zeros((cap, din), np.float32); self.D = np.zeros(cap, np.float32); self.n = 0; self.i = 0; self.cap = cap

    def add(self, trans):
        for s, a, r, s2, d in trans:
            self.S[self.i], self.A[self.i], self.R[self.i], self.S2[self.i], self.D[self.i] = s, a, r, s2, d
            self.i = (self.i + 1) % self.cap; self.n = min(self.n + 1, self.cap)

    def policy(self, eps):
        def f(O):
            with torch.no_grad():
                a = self.net(torch.as_tensor(O)).argmax(1).numpy()
            if eps > 0:
                a = np.where(self.rng.random(len(a)) < eps, self.rng.integers(0, self.nact, len(a)), a)
            return a
        return f

    def train(self, steps, bs=256):
        if self.n < bs:
            return float('nan')
        tot = 0.0
        for _ in range(steps):
            j = self.rng.integers(0, self.n, bs); S, A, R, S2, D = (torch.as_tensor(x[j]) for x in (self.S, self.A, self.R, self.S2, self.D))
            with torch.no_grad():
                a2 = self.net(S2).argmax(1, keepdim=True); y = R + self.gamma * (1 - D) * self.tgt(S2).gather(1, a2)[:, 0]
            q = self.net(S).gather(1, A[:, None])[:, 0]; loss = nn.functional.smooth_l1_loss(q, y)
            self.opt.zero_grad(); loss.backward(); nn.utils.clip_grad_norm_(self.net.parameters(), 5.0); self.opt.step(); tot += loss.item()
            with torch.no_grad():
                for p, pt in zip(self.net.parameters(), self.tgt.parameters()):
                    pt.mul_(0.99).add_(0.01 * p)
        return tot / steps


def load_policy(ckpt):
    net = torch.load(ckpt, weights_only=False)['net']; net.eval()
    return lambda O: net(torch.as_tensor(O)).argmax(1).numpy()


def eps_at(ep, E):
    return max(0.05, 1.0 - 0.95 * ep / max(1, int(0.6 * E)))


def train(a, out, kind):
    E = a.episodes; end = 300 if a.smoke else 3600; info = NetInfo(NET_S); log = []; t0 = time.perf_counter()
    if kind == 'light':
        agent = DQN(7, 2, 0.9, 11); fleet = load_policy(a.with_fleet) if a.with_fleet else None; steps = 200
    else:
        agent = DQN(6, NA_CAR, 0.97, 13); light_pol = None if a.against == 'ACT' else load_policy(a.against); steps = 400
    tmax = [0.0, 0.0]
    for ep in range(E):
        seed = TRAIN_SEEDS[ep % len(TRAIN_SEEDS)]; eps = eps_at(ep, E)
        if kind == 'light':
            light = LightRL(info, agent.policy(eps), record=True); cars = CarRL(fleet, RHO, seed) if fleet else None
            m = run_episode(NET_S, ROU.format(seed), seed, light, cars, end=end); trans = light.trans
        else:
            light = None if light_pol is None else LightRL(info, light_pol)
            cars = CarRL(agent.policy(eps), RHO, seed, record=True)
            m = run_episode(NET_A if light is None else NET_S, ROU.format(seed), seed, light, cars, end=end); trans = cars.trans
            for g, tau in cars.oos_log:
                tmax[int(g)] = max(tmax[int(g)], tau)
        agent.add(trans); loss = agent.train(steps if not a.smoke else 5)
        r = float(np.mean([t[2] for t in trans])) if trans else float('nan')
        log.append(dict(ep=ep, seed=seed, eps=eps, n=len(trans), mean_r=r, loss=loss, teleports=m['teleports'], wall=time.perf_counter() - t0))
        print(f'[{time.perf_counter() - t0:.0f}s] {a.name} ep {ep} eps {eps:.2f} trans {len(trans)} mean r {r:.3f} loss {loss:.4f} tele {m["teleports"]}', flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=agent.net, kind=kind, name=a.name, with_fleet=a.with_fleet, against=a.against, tmax=tmax, source_sha256=SRC,
                    episodes=E, smoke=a.smoke), out / f'{a.name}.pt')
    print(f'saved {out / (a.name + ".pt")}  tmax(red, green) {tmax}', flush=True)


def evaluate(a, out):
    import sumolib, libsumo as ls
    info = NetInfo(NET_S); end = 900 if a.smoke else 5400; seeds = EVAL_SEEDS[:1] if a.smoke else EVAL_SEEDS
    P = lambda n: str(out / f'{n}.pt')
    lights = {'FT': None, 'ACT': 'ACT', 'RL-H': P('RL-H'), 'RL-C': P('RL-H'), 'RL-J': P('RL-J')}
    fleets = {'human': None, 'L-ACT': P('L-ACT'), 'L-RLH': P('L-RLH')}
    configs = [(L, 'human') for L in lights] + [(L, 'L-ACT') for L in lights] + [('RL-H', 'L-RLH'), ('RL-C', 'L-RLH')]
    rows = []; t0 = time.perf_counter()
    for L, F in configs:
        for s in seeds:
            light = None
            if lights[L] not in (None, 'ACT'):
                light = LightRL(info, load_policy(lights[L]), max_g=MAXG_COMPAT if L == 'RL-C' else None)
            cars = CarRL(load_policy(fleets[F]), RHO, s, record=True) if fleets[F] else None
            ti = out / 'tripinfo' / f'{L}_{F}_s{s}.xml'; ti.parent.mkdir(parents=True, exist_ok=True)
            green_beyond = [0, 0]

            class Logger:                                   # light-side log: green-seconds beyond ACT's maxDur
                def step(self, t):
                    for tid, d in info.tls.items():
                        if ls.trafficlight.getPhase(tid) in d['greens']:
                            green_beyond[1] += 1; green_beyond[0] += ls.trafficlight.getSpentDuration(tid) > MAXG_COMPAT

            ctrl = [c for c in (light, cars, Logger()) if c is not None]

            class Multi:
                def step(self, t):
                    for c in ctrl:
                        c.step(t)
            net = NET_A if L == 'ACT' else NET_S
            m = run_episode(net, ROU.format(s), s, Multi(), None, end=end, tripinfo=str(ti))
            tl = [float(x.timeLoss) for x in sumolib.xml.parse(str(ti), 'tripinfo')]
            row = dict(light=L, fleet=F, seed=s, timeloss=float(np.mean(tl)), n=len(tl), teleports=m['teleports'],
                       green_beyond_50=green_beyond[0] / max(1, green_beyond[1]))
            if cars is not None:
                tr = cars.trans; done = sum(t[4] for t in tr); row['approach_cost'] = float(-sum(t[2] for t in tr) / max(1, done))
                row['n_approaches'] = int(done)
                tm = torch.load(fleets[F], weights_only=False)['tmax']; lg = np.array(cars.oos_log) if cars.oos_log else np.zeros((0, 2))
                row['tau_oos_mass'] = float(np.mean(lg[:, 1] > np.where(lg[:, 0] > 0.5, tm[1], tm[0]))) if len(lg) else float('nan')
            rows.append(row); (out / 'eval_rows.json').write_text(json.dumps(rows, indent=1))
            print(f'[{time.perf_counter() - t0:.0f}s] {L} × {F} s{s}: TL {row["timeloss"]:.1f} cost {row.get("approach_cost", float("nan")):.2f} '
                  f'oos {row.get("tau_oos_mass", float("nan")):.3f} >50s {row["green_beyond_50"]:.3f} tele {row["teleports"]}', flush=True)
    report(rows, out)


def report(rows, out):
    def M(L, F, k):
        v = [r[k] for r in rows if r['light'] == L and r['fleet'] == F and k in r]; return float(np.mean(v)) if v else float('nan')

    def paired(L1, F1, L2, F2, k):
        a = {r['seed']: r[k] for r in rows if r['light'] == L1 and r['fleet'] == F1 and k in r}
        b = {r['seed']: r[k] for r in rows if r['light'] == L2 and r['fleet'] == F2 and k in r}
        d = np.array([a[s] - b[s] for s in a if s in b]); rng = np.random.default_rng(0)
        bs = [d[rng.integers(0, len(d), len(d))].mean() for _ in range(4000)] if len(d) else [np.nan]
        return float(d.mean()) if len(d) else float('nan'), [float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))]
    L = ['Q7 mean time loss (s/veh) by light (rows) and fleet; agent approach cost in brackets']
    for Lt in ('FT', 'ACT', 'RL-H', 'RL-C', 'RL-J'):
        L.append(f'{Lt} | human {M(Lt, "human", "timeloss"):.1f} | L-ACT {M(Lt, "L-ACT", "timeloss"):.1f} [{M(Lt, "L-ACT", "approach_cost"):.2f}, oos {M(Lt, "L-ACT", "tau_oos_mass"):.3f}]'
                 + (f' | L-RLH {M(Lt, "L-RLH", "timeloss"):.1f} [{M(Lt, "L-RLH", "approach_cost"):.2f}]' if Lt in ('RL-H', 'RL-C') else '')
                 + f' | green>50s (human) {M(Lt, "human", "green_beyond_50"):.3f}')
    pred = {}
    ga, gf, gh = M('ACT', 'human', 'timeloss'), M('FT', 'human', 'timeloss'), M('RL-H', 'human', 'timeloss')
    pred['Q7-1 RL-H >= 5 % better than ACT and better than FT (human traffic)'] = dict(RLH=gh, ACT=ga, FT=gf, pass_=bool(gh <= 0.95 * ga and gh < gf))
    dc, ci = paired('RL-H', 'L-ACT', 'RL-H', 'L-RLH', 'approach_cost')
    pred['Q7-2 Delta_car > 0 (L-ACT vs L-RLH under RL-H)'] = dict(delta=dc, ci=ci, pass_=bool(ci[0] > 0))
    gb, oo = M('RL-H', 'human', 'green_beyond_50'), M('RL-H', 'L-ACT', 'tau_oos_mass')
    pred['Q7-3 certificate: RL-H green>50s >= 10 % and fleet tau OOS >= 10 %'] = dict(green_beyond=gb, oos=oo, pass_=bool(gb >= 0.10 and oo >= 0.10))
    gc = M('RL-C', 'human', 'timeloss'); keep = (ga - gc) / (ga - gh) if ga != gh else float('nan')
    dcc = M('RL-C', 'L-ACT', 'approach_cost') - M('RL-H', 'L-RLH', 'approach_cost')
    pred['Q7-4 compatible mode keeps >= 80 % of the gain and halves Delta_car'] = dict(keep=keep, delta_compat=dcc, delta=dc,
                                                                                    pass_=bool(keep >= 0.8 and dcc <= 0.5 * dc))
    rel = lambda Lt: M(Lt, 'L-ACT', 'timeloss') / M(Lt, 'human', 'timeloss') - 1
    ex_h, ex_j = rel('RL-H') - rel('FT'), rel('RL-J') - rel('FT')
    pred['Q7-5 car -> light: RL-H excess over FT >= 5 points; RL-J recovers >= half'] = dict(excess_RLH=ex_h, excess_RLJ=ex_j, excess_ACT=rel('ACT') - rel('FT'),
                                                                                         pass_=bool(ex_h >= 0.05 and ex_j <= 0.5 * ex_h))
    L += [f'{k}: {"SUPPORTED" if v["pass_"] else "NOT SUPPORTED"} {json.dumps({kk: vv for kk, vv in v.items() if kk != "pass_"})}' for k, v in pred.items()]
    txt = '\n'.join(L); print(txt, flush=True); (out / 'report.txt').write_text(txt + '\n')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', source_sha256=SRC, protocol='research/city_sim/PROTOCOL_CITY_Q7_CROSS_VERSION_20261002.md'), indent=1))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--out', required=True); ap.add_argument('--smoke', action='store_true')
    ap.add_argument('--train-light', dest='light_name'); ap.add_argument('--with-fleet', dest='with_fleet', default=None)
    ap.add_argument('--train-fleet', dest='fleet_name'); ap.add_argument('--against', default='ACT')
    ap.add_argument('--episodes', type=int, default=120); ap.add_argument('--eval', action='store_true')
    a = ap.parse_args(); out = Path(a.out); out.mkdir(parents=True, exist_ok=True); torch.set_num_threads(1)
    if a.light_name:
        a.name = a.light_name; train(a, out, 'light')
    elif a.fleet_name:
        a.name = a.fleet_name; train(a, out, 'fleet')
    elif a.eval:
        evaluate(a, out)
