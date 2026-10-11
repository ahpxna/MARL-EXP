#!/usr/bin/env python3
"""Two-population cross-play (B1) and the hidden-queue sensing test (B1b) — research/city_sim/PROTOCOL_CITY_XPLAY_HCRAWL_20261004.md
(04/10/2026, wake 1).  One configuration (light setting x fleet) over evaluation seeds per call; existing checkpoints only.
  --light ACT | RL-H:t | RL-J:t | RL-C50:t     (t = 0 reads research/city_sim/q7_cross_version_20261002, t >= 1 q7b_contract_20261002)
  --fleet human | L-ACT:t | L-RLH:0
  --sense default | crawl                       crawl: the light's two halting features count v < 2.0 m/s instead of SUMO halting
The evaluation path is Q7b's (scripts/CITY_q7b_contract.evaluate): controllers stepped in the order light, cars, logger inside
run_episode, tripinfo with unfinished trips, 5400 s, rho 0.5; the logger only reads.  Extra per-run metrics: human / agent time
loss, finished / unfinished trips, and per light decision the halting / crawling / moving counts on the served lanes split agent /
human (hidden-queue share = crawling / (halting + crawling)).
SELF-CHECK (in the report): every configuration that exists in Q7b reproduces its stored time loss and approach cost exactly."""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, CarRL, run_episode  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402

Q7DIR = ROOT / 'research/city_sim/q7_cross_version_20261002'; Q7BDIR = ROOT / 'research/city_sim/q7b_contract_20261002'
CRAWL = 2.0
SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def ckpt(kind, t):
    t = int(t)
    return Q7DIR / f'{kind}.pt' if t == 0 else Q7BDIR / f'{kind}_t{t}.pt'


class LightRLCrawl(LightRL):
    """Same weights and decision rule; the two halting features count vehicles slower than CRAWL m/s (honest physical count)."""

    def obs(self, tid):
        ls = CE.ls; d = self.info.tls[tid]; ph = ls.trafficlight.getPhase(tid)
        h = [sum(sum(1 for v in ls.lane.getLastStepVehicleIDs(l) if ls.vehicle.getSpeed(v) < CRAWL) for l in s) for s in d['serve']]
        n = [sum(ls.lane.getLastStepVehicleNumber(l) for l in s) for s in d['serve']]
        cur = d['greens'].index(ph) if ph in d['greens'] else -1
        return np.array([h[0] / 10, h[1] / 10, n[0] / 20, n[1] / 20, cur == 0, cur == 1, ls.trafficlight.getSpentDuration(tid) / 60],
                        np.float32), sum(h), cur


def run(a, seed, end):
    import sumolib
    ls = CE.ls; info = NetInfo(Q7.NET_S); lk, _, lt = a.light.partition(':'); fk, _, ft = a.fleet.partition(':')
    if lk == 'ACT':
        light, net = None, Q7.NET_A
    else:
        cls = LightRLCrawl if a.sense == 'crawl' else LightRL
        light = cls(info, Q7.load_policy(ckpt('RL-H' if lk == 'RL-C50' else lk, lt)), max_g=50 if lk == 'RL-C50' else None); net = Q7.NET_S
    cars, tm = None, None
    if fk != 'human':
        fc = ckpt(fk, ft); cars = CarRL(Q7.load_policy(fc), Q7.RHO, seed, record=True); tm = torch.load(fc, weights_only=False)['tmax']
    cnt = dict(halt_a=0, crawl_a=0, move_a=0, halt_h=0, crawl_h=0, move_h=0)

    class Logger:
        def step(self, t):
            if int(t) % CE.DT_L:
                return
            for tid, d in info.tls.items():
                for s in d['serve']:
                    for l in s:
                        for v in ls.lane.getLastStepVehicleIDs(l):
                            sp = ls.vehicle.getSpeed(v); k = 'halt' if sp < 0.1 else ('crawl' if sp < CRAWL else 'move')
                            cnt[f"{k}_{'a' if cars is not None and cars.is_agent(v) else 'h'}"] += 1
    ctrl = [c for c in (light, cars, Logger()) if c is not None]

    class Multi:
        def step(self, t):
            for c in ctrl:
                c.step(t)
    ti = Path(a.out) / 'tripinfo' / f'{a.light}_{a.fleet}_{a.sense}_s{seed}.xml'.replace(':', '')
    ti.parent.mkdir(parents=True, exist_ok=True)
    m = run_episode(net, Q7.ROU.format(seed), seed, Multi(), None, end=end, tripinfo=str(ti))
    trips = [(x.id, float(x.timeLoss), float(x.arrival) >= 0) for x in sumolib.xml.parse(str(ti), 'tripinfo')]
    ag = (lambda v: cars.is_agent(v)) if cars is not None else (lambda v: False)
    tl = [x[1] for x in trips]; tla = [x[1] for x in trips if ag(x[0])]; tlh = [x[1] for x in trips if not ag(x[0])]
    row = dict(light=a.light, fleet=a.fleet, sense=a.sense, seed=seed, timeloss=float(np.mean(tl)), n=len(tl),
               timeloss_agent=float(np.mean(tla)) if tla else float('nan'), timeloss_human=float(np.mean(tlh)) if tlh else float('nan'),
               finished=int(sum(x[2] for x in trips)), unfinished=int(sum(not x[2] for x in trips)), teleports=m['teleports'], **cnt)
    for g in ('a', 'h'):
        row[f'hidden_{g}'] = cnt[f'crawl_{g}'] / max(1, cnt[f'crawl_{g}'] + cnt[f'halt_{g}'])
    if cars is not None:
        tr = cars.trans; done = sum(x[4] for x in tr); row['approach_cost'] = float(-sum(x[2] for x in tr) / max(1, done))
        lg = np.array(cars.oos_log) if cars.oos_log else np.zeros((0, 2))
        row['tau_oos_mass'] = float(np.mean(lg[:, 1] > np.where(lg[:, 0] > 0.5, tm[1], tm[0]))) if len(lg) else float('nan')
    return row


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); tag = f'{a.light}_{a.fleet}_{a.sense}'.replace(':', '')
    fn = out / f'{tag}.json'
    if fn.exists() and json.loads(fn.read_text()).get('status') == 'COMPLETE':
        print('skip', tag); return
    rows = []; t0 = time.perf_counter(); end = 600 if a.smoke else 5400
    for s in (a.seeds[:1] if a.smoke else a.seeds):
        r = run(a, s, end); rows.append(r)
        print(f"[{time.perf_counter() - t0:.0f}s] {tag} s{s}: TL {r['timeloss']:.2f} (agent {r['timeloss_agent']:.2f} human {r['timeloss_human']:.2f}) "
              f"cost {r.get('approach_cost', float('nan')):.3f} hidden a {r['hidden_a']:.3f} h {r['hidden_h']:.3f} unfinished {r['unfinished']}", flush=True)
    lk, _, lt = a.light.partition(':'); fk, _, ft = a.fleet.partition(':')
    ck = {}
    if lk != 'ACT':
        p = ckpt('RL-H' if lk == 'RL-C50' else lk, lt); ck['light'] = hashlib.sha256(p.read_bytes()).hexdigest()
    if fk != 'human':
        ck['fleet'] = hashlib.sha256(ckpt(fk, ft).read_bytes()).hexdigest()
    fn.write_text(json.dumps(dict(status='COMPLETE', rows=rows, args=vars(a), source_sha256=SRC, ckpt_sha256=ck,
                                  env_sha256=hashlib.sha256((ROOT / 'scripts/CITY_env.py').read_bytes()).hexdigest()), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--light', required=True); p.add_argument('--fleet', required=True); p.add_argument('--sense', default='default', choices=['default', 'crawl'])
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--out', required=True)
    main(p.parse_args())
