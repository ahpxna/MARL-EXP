#!/usr/bin/env python3
"""B3-X of research/city_sim/PROTOCOL_CITY_COTRAIN_20261004.md (04/10/2026 wake 2): one (light, fleet) configuration over evaluation seeds
per call — CITY_xplay.run's evaluation path with a general checkpoint resolver.  Run with PYTHONHASHSEED=0.
  lights: ACT | FT | RL-H:t | RL-J:t | RL-C50:t | <ARM>:k   (ARM in SIM-halt, ALT-halt, SIM-delay, ...: cotrain_20261004/<ARM>_k<k>_light.pt)
  fleets: human | L-ACT:t | L-FT:t | L-RLH:t | <ARM>:k      (L-RLH:0 = Q7's L-RLH.pt, L-RLH:t>=1 = cotrain_20261004/L-RLH_t<t>_fleet.pt)
SELF-CHECK (report): every configuration that is also in the h0 panel (xplay_h0_20261004) is bit-identical to it."""
from __future__ import annotations
import argparse, hashlib, json, os, sys, tempfile, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_env as CE  # noqa: E402
from scripts.CITY_env import NetInfo, LightRL, CarRL, run_episode  # noqa: E402
import scripts.CITY_q7_cross_version as Q7  # noqa: E402

Q7DIR = ROOT / 'research/city_sim/q7_cross_version_20261002'; Q7BDIR = ROOT / 'research/city_sim/q7b_contract_20261002'
COT = ROOT / 'research/city_sim/cotrain_20261004'; CRAWL = 2.0
SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def light_spec(s):
    """-> (net, checkpoint or None, max_g)"""
    k, _, t = s.partition(':')
    if k == 'ACT':
        return Q7.NET_A, None, None
    if k == 'FT':
        return Q7.NET_S, None, None
    if k in ('RL-H', 'RL-J', 'RL-C50'):
        base = 'RL-H' if k == 'RL-C50' else k
        return Q7.NET_S, (Q7DIR / f'{base}.pt' if int(t) == 0 else Q7BDIR / f'{base}_t{t}.pt'), (50 if k == 'RL-C50' else None)
    return Q7.NET_S, COT / f'{k}_k{t}_light.pt', None


def fleet_ckpt(s):
    k, _, t = s.partition(':')
    if k == 'human':
        return None
    if k == 'L-ACT':
        return Q7DIR / 'L-ACT.pt' if int(t) == 0 else Q7BDIR / f'L-ACT_t{t}.pt'
    if k == 'L-FT':
        return Q7BDIR / f'L-FT_t{t}.pt'
    if k == 'L-RLH':
        return Q7DIR / 'L-RLH.pt' if int(t) == 0 else COT / f'L-RLH_t{t}_fleet.pt'
    return COT / f'{k}_k{t}_fleet.pt'


def run(a, seed, end):
    import sumolib
    ls = CE.ls; info = NetInfo(Q7.NET_S); net, lck, mg = light_spec(a.light); fck = fleet_ckpt(a.fleet)
    light = LightRL(info, Q7.load_policy(lck), max_g=mg) if lck is not None else None
    cars, tm = None, None
    if fck is not None:
        cars = CarRL(Q7.load_policy(fck), Q7.RHO, seed, record=True); d = torch.load(fck, weights_only=False)
        tm = d.get('tmax_late') or d['tmax']
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
    fd, ti = tempfile.mkstemp(suffix='.xml', prefix='xplay2_', dir=os.environ.get('XPLAY_TMP')); os.close(fd)   # temporary per-vehicle XML
    m = run_episode(net, Q7.ROU.format(seed), seed, Multi(), None, end=end, tripinfo=str(ti))
    trips = [(x.id, float(x.timeLoss), float(x.arrival) >= 0) for x in sumolib.xml.parse(str(ti), 'tripinfo')]
    ag = (lambda v: cars.is_agent(v)) if cars is not None else (lambda v: False)
    tl = [x[1] for x in trips]; tla = [x[1] for x in trips if ag(x[0])]; tlh = [x[1] for x in trips if not ag(x[0])]
    row = dict(light=a.light, fleet=a.fleet, sense='default', seed=seed, timeloss=float(np.mean(tl)), n=len(tl),
               timeloss_agent=float(np.mean(tla)) if tla else float('nan'), timeloss_human=float(np.mean(tlh)) if tlh else float('nan'),
               finished=int(sum(x[2] for x in trips)), unfinished=int(sum(not x[2] for x in trips)), teleports=m['teleports'], **cnt)
    for g in ('a', 'h'):
        row[f'hidden_{g}'] = cnt[f'crawl_{g}'] / max(1, cnt[f'crawl_{g}'] + cnt[f'halt_{g}'])
    if cars is not None:
        tr = cars.trans; done = sum(x[4] for x in tr); row['approach_cost'] = float(-sum(x[2] for x in tr) / max(1, done))
        lg = np.array(cars.oos_log) if cars.oos_log else np.zeros((0, 2))
        row['tau_oos_mass'] = float(np.mean(lg[:, 1] > np.where(lg[:, 0] > 0.5, tm[1], tm[0]))) if len(lg) else float('nan')
    os.remove(ti)                                              # a temporary file in XPLAY_TMP: the rows are the artifact
    return row


def main(a):
    if os.environ.get('PYTHONHASHSEED') != '0':
        sys.exit('run with PYTHONHASHSEED=0')
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); tag = f'{a.light}_{a.fleet}'.replace(':', '')
    fn = out / f'{tag}.json'
    if fn.exists() and json.loads(fn.read_text()).get('status') == 'COMPLETE':
        print('skip', tag); return
    rows = []; t0 = time.perf_counter(); end = 600 if a.smoke else 5400
    for s in (a.seeds[:1] if a.smoke else a.seeds):
        r = run(a, s, end); rows.append(r)
        print(f"[{time.perf_counter() - t0:.0f}s] {tag} s{s}: TL {r['timeloss']:.2f} (agent {r['timeloss_agent']:.2f} human {r['timeloss_human']:.2f}) "
              f"cost {r.get('approach_cost', float('nan')):.3f} tele {r['teleports']} unfinished {r['unfinished']}", flush=True)
    ck = {}
    _, lck, _ = light_spec(a.light); fck = fleet_ckpt(a.fleet)
    if lck is not None:
        ck['light'] = hashlib.sha256(Path(lck).read_bytes()).hexdigest()
    if fck is not None:
        ck['fleet'] = hashlib.sha256(Path(fck).read_bytes()).hexdigest()
    fn.write_text(json.dumps(dict(status='COMPLETE', rows=rows, args=vars(a), source_sha256=SRC, ckpt_sha256=ck, pythonhashseed=os.environ.get('PYTHONHASHSEED'),
                                  env_sha256=hashlib.sha256((ROOT / 'scripts/CITY_env.py').read_bytes()).hexdigest()), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--light', required=True); p.add_argument('--fleet', required=True)
    p.add_argument('--seeds', type=int, nargs='+', default=[100, 101, 102, 103, 104]); p.add_argument('--smoke', action='store_true')
    p.add_argument('--out', required=True)
    main(p.parse_args())
