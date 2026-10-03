#!/usr/bin/env python3
"""Q7b (research/city_sim/PROTOCOL_CITY_Q7B_CONTRACT_20261002.md, written 23:0x EDT 02/10/2026): Q7 across training seeds, the
compatible-mode frontier over the forced-switch cap, and the receiver-contract certificate.  Imports the Q7 classes unchanged
(scripts/CITY_q7_cross_version.py: DQN, load_policy, eps_at; scripts/CITY_env.py).  Modes:
  --train-light NAME --t T [--with-fleet CKPT]   RL-H_t / RL-J_t (DQN seed 11 + 100 T)
  --train-fleet NAME --t T [--against ACT|FT]    L-ACT_t against SUMO actuated, L-FT_t against the static program (13 + 100 T)
  --eval --t T [--q7dir DIR]                     lights FT, ACT, RL-H_t, RL-C(c)_t (c in CAPS), RL-J_t x fleets human, L-ACT_t;
                                                  t = 0 reads the Q7 checkpoints from --q7dir
  --report                                       B1-B4 over every evaluated t
Usage: CITY_q7b_contract.py --out DIR <mode> [--episodes 120] [--smoke]"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_env import NetInfo, LightRL, CarRL, run_episode, NA_CAR  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402

NET_S, NET_A, ROU, TRAIN_SEEDS, EVAL_SEEDS, RHO = Q7.NET_S, Q7.NET_A, Q7.ROU, Q7.TRAIN_SEEDS, Q7.EVAL_SEEDS, Q7.RHO
CAPS = [30, 40, 50, 60, 80, 120]
SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def train(a, out, kind):
    """Q7.train with the DQN seed shifted by 100 t (everything else identical)."""
    E = a.episodes; end = 300 if a.smoke else 3600; info = NetInfo(NET_S); log = []; t0 = time.perf_counter()
    if kind == 'light':
        agent = Q7.DQN(7, 2, 0.9, 11 + 100 * a.t); fleet = Q7.load_policy(a.with_fleet) if a.with_fleet else None; steps = 200
    else:
        agent = Q7.DQN(6, NA_CAR, 0.97, 13 + 100 * a.t); steps = 400; net_f = NET_A if a.against == 'ACT' else NET_S
    tmax = [0.0, 0.0]
    for ep in range(E):
        seed = TRAIN_SEEDS[ep % len(TRAIN_SEEDS)]; eps = Q7.eps_at(ep, E)
        if kind == 'light':
            light = LightRL(info, agent.policy(eps), record=True); cars = CarRL(fleet, RHO, seed) if fleet else None
            m = run_episode(NET_S, ROU.format(seed), seed, light, cars, end=end); trans = light.trans
        else:
            cars = CarRL(agent.policy(eps), RHO, seed, record=True)
            m = run_episode(net_f, ROU.format(seed), seed, None, cars, end=end); trans = cars.trans
            for g, tau in cars.oos_log:
                tmax[int(g)] = max(tmax[int(g)], tau)
        agent.add(trans); loss = agent.train(steps if not a.smoke else 5)
        r = float(np.mean([x[2] for x in trans])) if trans else float('nan')
        log.append(dict(ep=ep, seed=seed, eps=eps, n=len(trans), mean_r=r, loss=loss, teleports=m['teleports'], wall=time.perf_counter() - t0))
        print(f'[{time.perf_counter() - t0:.0f}s] {a.name} t{a.t} ep {ep} eps {eps:.2f} trans {len(trans)} mean r {r:.3f} loss {loss:.4f}', flush=True)
        (out / f'{a.name}.log.json').write_text(json.dumps(log))
    torch.save(dict(net=agent.net, kind=kind, name=a.name, t=a.t, with_fleet=a.with_fleet, against=a.against, tmax=tmax, source_sha256=SRC, episodes=E,
                    smoke=a.smoke), out / f'{a.name}.pt')
    print(f'saved {out / (a.name + ".pt")} tmax {tmax}', flush=True)


def ckpts(a, out):
    if a.t == 0:
        d = Path(a.q7dir); return {'RL-H': d / 'RL-H.pt', 'RL-J': d / 'RL-J.pt', 'L-ACT': d / 'L-ACT.pt', 'L-FT': out / 'L-FT_t0.pt'}
    return {'RL-H': out / f'RL-H_t{a.t}.pt', 'RL-J': out / f'RL-J_t{a.t}.pt', 'L-ACT': out / f'L-ACT_t{a.t}.pt', 'L-FT': out / f'L-FT_t{a.t}.pt'}


def evaluate(a, out):
    import sumolib, libsumo as ls
    info = NetInfo(NET_S); end = 900 if a.smoke else 5400; seeds = EVAL_SEEDS[:1] if a.smoke else EVAL_SEEDS; C = ckpts(a, out)
    tm = torch.load(C['L-ACT'], weights_only=False)['tmax']                      # the receiver's published region (contract)
    lights = {'FT': (None, None), 'ACT': ('ACT', None), 'RL-H': (C['RL-H'], None), 'RL-J': (C['RL-J'], None)}
    for c in CAPS:
        lights[f'RL-C{c}'] = (C['RL-H'], c)
    fleets = {'human': None, 'L-ACT': C['L-ACT'], 'L-FT': C['L-FT']}
    rows = []; t0 = time.perf_counter(); fn = out / f'eval_t{a.t}.json'
    for L, (ck, cap) in lights.items():
        for F in fleets:
            if F == 'L-FT' and L != 'FT':
                continue
            for s in seeds:
                light = LightRL(info, Q7.load_policy(ck), max_g=cap) if ck not in (None, 'ACT') else None
                cars = CarRL(Q7.load_policy(fleets[F]), RHO, s, record=True) if fleets[F] else None
                ti = out / 'tripinfo' / f't{a.t}_{L}_{F}_s{s}.xml'; ti.parent.mkdir(parents=True, exist_ok=True)
                acc = dict(free=[0, 0], con=[0.0, 0.0])

                class Logger:                       # the LIGHT's own log: phase time, colour per controlled lane, vehicles on it
                    def step(self, t):
                        for tid, d in info.tls.items():
                            tau = ls.trafficlight.getSpentDuration(tid); ph = ls.trafficlight.getPhase(tid)
                            if ph in d['greens']:
                                acc['free'][1] += 1; acc['free'][0] += tau > 50
                            st = ls.trafficlight.getRedYellowGreenState(tid); seen = set()
                            for k, ln in enumerate(ls.trafficlight.getControlledLanes(tid)):
                                if ln in seen:
                                    continue
                                seen.add(ln); n = ls.lane.getLastStepVehicleNumber(ln)
                                if n:
                                    g = 1 if st[k] in 'Gg' else 0
                                    acc['con'][1] += n; acc['con'][0] += n * (tau > tm[g])
                ctrl = [c for c in (light, cars, Logger()) if c is not None]

                class Multi:
                    def step(self, t):
                        for c in ctrl:
                            c.step(t)
                m = run_episode(NET_A if L == 'ACT' else NET_S, ROU.format(s), s, Multi(), None, end=end, tripinfo=str(ti))
                tl = [float(x.timeLoss) for x in sumolib.xml.parse(str(ti), 'tripinfo')]
                row = dict(t=a.t, light=L, fleet=F, seed=s, timeloss=float(np.mean(tl)), n=len(tl), teleports=m['teleports'],
                           K_free=acc['free'][0] / max(1, acc['free'][1]), K_contract=acc['con'][0] / max(1e-9, acc['con'][1]))
                if cars is not None:
                    tr = cars.trans; done = sum(x[4] for x in tr); row['approach_cost'] = float(-sum(x[2] for x in tr) / max(1, done))
                    lg = np.array(cars.oos_log) if cars.oos_log else np.zeros((0, 2))
                    row['tau_oos_mass'] = float(np.mean(lg[:, 1] > np.where(lg[:, 0] > 0.5, tm[1], tm[0]))) if len(lg) else float('nan')
                rows.append(row); fn.write_text(json.dumps(rows, indent=1))
                print(f'[{time.perf_counter() - t0:.0f}s] t{a.t} {L} x {F} s{s}: TL {row["timeloss"]:.1f} cost {row.get("approach_cost", float("nan")):.2f} '
                      f'oos {row.get("tau_oos_mass", float("nan")):.3f} Kfree {row["K_free"]:.3f} Kcon {row["K_contract"]:.3f}', flush=True)
    (out / f'eval_t{a.t}.manifest.json').write_text(json.dumps(dict(status='COMPLETE', t=a.t, source_sha256=SRC, q7_source_sha256=Q7.SRC,
        ckpt_sha256={k: hashlib.sha256(Path(v).read_bytes()).hexdigest() for k, v in C.items()}, smoke=a.smoke), indent=1))


def spearman(x, y):
    rx = np.argsort(np.argsort(x)); ry = np.argsort(np.argsort(y)); return float(np.corrcoef(rx, ry)[0, 1])


def report(a, out):
    rows = []; ts = []
    for f in sorted(out.glob('eval_t*.json')):
        if f.name.endswith('manifest.json'):
            continue
        if not (out / f.name.replace('.json', '.manifest.json')).exists():
            continue
        rows += json.loads(f.read_text()); ts.append(int(f.stem.split('_t')[1]))
    ts = sorted(set(ts))
    M = lambda t, L, F, k: float(np.mean([r[k] for r in rows if r['t'] == t and r['light'] == L and r['fleet'] == F and k in r]))
    def reg(t, L):                                          # paired regression of the deployed fleet vs its old light ACT
        a_ = {r['seed']: r['approach_cost'] for r in rows if r['t'] == t and r['light'] == L and r['fleet'] == 'L-ACT'}
        b_ = {r['seed']: r['approach_cost'] for r in rows if r['t'] == t and r['light'] == 'ACT' and r['fleet'] == 'L-ACT'}
        d = np.array([a_[s] - b_[s] for s in a_ if s in b_]); rng = np.random.default_rng(0)
        bs = [d[rng.integers(0, len(d), len(d))].mean() for _ in range(4000)]
        return float(d.mean()), [float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))]
    gain = lambda t, L: M(t, 'ACT', 'human', 'timeloss') - M(t, L, 'human', 'timeloss')
    Lines = [f'Q7b over training seeds {ts}: light gain g (s/veh vs ACT, human traffic), fleet regression r (approach cost vs ACT) [95 %], '
             'K_free / K_contract (light logs, human traffic) / cross-play OOS']
    lights = ['FT', 'ACT', 'RL-H'] + [f'RL-C{c}' for c in CAPS] + ['RL-J']
    for t in ts:
        for L in lights:
            r_, ci = reg(t, L)
            Lines.append(f't{t} {L} | g {gain(t, L):+.2f} | r {r_:+.2f} {[round(v, 2) for v in ci]} | K_free {M(t, L, "human", "K_free"):.3f} | '
                         f'K_contract {M(t, L, "human", "K_contract"):.3f} | OOS {M(t, L, "L-ACT", "tau_oos_mass"):.3f}')
    b1 = all(M(t, 'RL-H', 'human', 'timeloss') <= 0.95 * M(t, 'ACT', 'human', 'timeloss') and reg(t, 'RL-H')[1][0] > 0 for t in ts)
    caps = CAPS + [10 ** 6]; nm = lambda c: 'RL-H' if c == 10 ** 6 else f'RL-C{c}'
    gc = [float(np.mean([gain(t, nm(c)) for t in ts])) for c in caps]; rc = [float(np.mean([reg(t, nm(c))[0] for t in ts])) for c in caps]
    viol = lambda v: sum(1 for i in range(len(v) - 1) if v[i + 1] < v[i] - 1e-9); big = lambda v: max([v[i] - v[i + 1] for i in range(len(v) - 1)] + [0])
    gH, rH = gc[-1], rc[-1]
    ok_c = [c for c, g_, r_ in zip(caps[:-1], gc[:-1], rc[:-1]) if c <= 60 and g_ >= 0.8 * gH and r_ <= 0.5 * rH]
    b2 = viol(gc) <= 1 and viol(rc) <= 1 and big(gc) <= 1 and big(rc) <= 1 and bool(ok_c)
    pts = [(t, L) for t in ts for L in lights if L != 'FT']
    R = [reg(t, L)[0] for t, L in pts]; KC = [M(t, L, 'human', 'K_contract') for t, L in pts]; KF = [M(t, L, 'human', 'K_free') for t, L in pts]
    OO = [M(t, L, 'L-ACT', 'tau_oos_mass') for t, L in pts]
    sc, sf = spearman(KC, R), spearman(KF, R)
    fac = all(0.5 * o <= k <= 2 * o for k, o in zip(KC, OO) if o >= 0.05)
    b3 = sc >= 0.7 and sc > sf and fac
    kft = float(np.mean([M(t, 'FT', 'human', 'K_contract') for t in ts])); rft = float(np.mean([reg(t, 'FT')[0] for t in ts]))
    b4 = kft <= 0.02 and rft >= 10
    def mis(t):                                            # B4': L-ACT's mismatch under FT vs the FT specialist, paired
        a_ = {r['seed']: r['approach_cost'] for r in rows if r['t'] == t and r['light'] == 'FT' and r['fleet'] == 'L-ACT'}
        b_ = {r['seed']: r['approach_cost'] for r in rows if r['t'] == t and r['light'] == 'FT' and r['fleet'] == 'L-FT'}
        return [a_[s] - b_[s] for s in a_ if s in b_]
    md = [x for t in ts for x in mis(t)]; mft = float(np.mean(md)) if md else float('nan')
    b4p = bool(md) and kft <= 0.02 and mft >= 10
    price = {c: 1 - gc[i] / gH if gH else float('nan') for i, c in enumerate(caps)}
    r50 = rc[caps.index(50)]; b5 = price[50] <= 0.15 and price[60] <= 0.15 and price[30] >= 2 * price[50] and rc[caps.index(30)] >= 0.5 * r50
    Lines += [f'frontier (mean over t; cap -> g, r): ' + ', '.join(f'{"inf" if c == 10 ** 6 else c}: {g_:+.2f}/{r_:+.2f}' for c, g_, r_ in zip(caps, gc, rc))]
    pr = {'B1 replication: RL-H_t >= 5 % better than ACT and r(RL-H_t) lower > 0 for every t': (b1, {}),
          'B2 frontier monotone (<= 1 violation of <= 1 per curve) and some c <= 60 keeps >= 80 % of g with r <= half': (b2, dict(caps_ok=ok_c)),
          'B3 contract certificate ranks the regression (Spearman >= 0.7, > K_free) and is within x2 of cross-play OOS': (b3, dict(spearman_contract=sc, spearman_free=sf, factor2=fac, n=len(pts))),
          'B4 FT: in-support (K_contract <= 0.02) yet regressed (r >= 10)': (b4, dict(K_contract=kft, r=rft)),
          "B4' FT: in-support and mismatched vs the FT specialist (m >= 10)": (b4p, dict(K_contract=kft, mismatch=mft, n=len(md))),
          'B5 knee at the receiver support: p(50), p(60) <= 0.15, p(30) >= 2 p(50), r(30) >= 0.5 r(50)': (b5, dict(price={str(k): v for k, v in price.items() if k != 10 ** 6}, r30=rc[caps.index(30)], r50=r50))}
    Lines += [f'{k}: {"SUPPORTED" if v else "NOT SUPPORTED"} {json.dumps(d)}' for k, (v, d) in pr.items()]
    KCF = [M(t, L, 'L-ACT', 'K_contract') for t, L in pts]            # reported (H2b): the closed-loop contract certificate
    Lines.append(f'reported (H2b): K_contract with the fleet present vs cross-play OOS: Spearman {spearman(KCF, OO):+.2f}, '
                 f'mean ratio {float(np.mean([k / o for k, o in zip(KCF, OO) if o >= 0.05] or [float("nan")])):.2f}; '
                 f'human-traffic K_contract mean ratio {float(np.mean([k / o for k, o in zip(KC, OO) if o >= 0.05] or [float("nan")])):.2f}; '
                 f'Spearman(K_contract with fleet, r) {spearman(KCF, R):+.2f}')
    txt = '\n'.join(Lines); print(txt, flush=True)
    if not a.smoke:
        (out / 'report.txt').write_text(txt + '\n')
        (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', source_sha256=SRC, t=ts, protocol='research/city_sim/PROTOCOL_CITY_Q7B_CONTRACT_20261002.md'), indent=1))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--out', required=True); ap.add_argument('--smoke', action='store_true')
    ap.add_argument('--train-light', dest='light_name'); ap.add_argument('--with-fleet', dest='with_fleet', default=None)
    ap.add_argument('--train-fleet', dest='fleet_name'); ap.add_argument('--t', type=int, default=1); ap.add_argument('--against', default='ACT', choices=['ACT', 'FT'])
    ap.add_argument('--episodes', type=int, default=120); ap.add_argument('--eval', action='store_true'); ap.add_argument('--report', action='store_true')
    ap.add_argument('--q7dir', default='research/city_sim/q7_cross_version_20261002')
    a = ap.parse_args(); out = Path(a.out); out.mkdir(parents=True, exist_ok=True); torch.set_num_threads(1)
    if a.light_name:
        a.name = a.light_name; train(a, out, 'light')
    elif a.fleet_name:
        a.name = a.fleet_name; train(a, out, 'fleet')
    elif a.eval:
        evaluate(a, out)
    elif a.report:
        report(a, out)
