#!/usr/bin/env python3
"""CHANNEL-COMPOSITION probe v2 (01/10/2026 23:4x EDT; PROTOCOL_E3_NET_COUNT_20261001.md Parts 1 and 4).  FIXED actions
only (first valid phase; at constant K and for age-based orders the composition does not depend on the policy).  v1's closed
loop (relay v2 merge 'age') with:
  --order agefirst | hub | countdeadline<tau>   (models/marl_delivery_music_v4.HubDelivery, models/marl_delivery_countdeadline.py)
  --hold r                                (models/marl_delivery_hold.HoldDelivery; age-first, mode prefix, constant K)
  --capacity iid | low | bursty | high | fixed | rich<k> | cap4 | const<k>  (02/10 01:1x: + bursty / high / fixed / rich<k>, the
                                          evaluators' constructions; cap4 = the cap4 rule on the iid trace)
Per cell: v1's fields (entries, never, stale = age > 2, B3, max-age percentiles, age histogram, B_tau) plus fresh F (age 0
entries), S_tau = entries older than tau (tau = 0..14) and the net count F - S_2 - never.
SELF-CHECK (--selfcheck): agefirst, hold 1, const K / iid must reproduce v1's g3_nopolicy composition.json exactly.
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_e3_actor_train import Scenarios
from scripts.MARL_hetero_panel_collect import capacity_trace
from models.marl_relay_v2 import merge_views as merge_views_v2
from models.marl_delivery_music import MusicDelivery
from models.marl_delivery_hold import HoldDelivery
from models.marl_delivery_countdeadline import CountDeadlineDelivery


def delivery(order, hold, cap):
    if order == 'agefirst':
        d = HoldDelivery(hold) if hold > 1 else MusicDelivery('agefirst')
    elif order == 'hub':
        if hold > 1:
            raise SystemExit('hold applies to age-first only')
        from models.marl_delivery_music_v4 import HubDelivery
        d = HubDelivery()
    elif order.startswith('countdeadline'):
        if hold > 1:
            raise SystemExit('hold applies to age-first only')
        d = CountDeadlineDelivery(float(order[len('countdeadline'):]))
    else:
        raise SystemExit(order)
    d.mode = 'cap4' if cap == 'cap4' else 'prefix'
    if hold > 1 and d.mode != 'prefix':
        raise SystemExit('hold needs mode prefix')
    return d


def run(sc, seed, load, order, hold, cap):
    env, topo, _, _ = sc.env(seed, load); m = env.n_agents
    if cap in ('low', 'bursty', 'high', 'fixed'):
        env._trace = capacity_trace(cap, N_DEC, m, 5000 + 10 * seed + int(load))
    elif cap.startswith('rich'):                           # exactly MARL_e3_delivery_eval_relay_v6.py's rich<k>
        tr = np.ones_like(np.asarray(env._trace)); g = np.random.default_rng([int(seed), int(round(float(load) * 10)), 0x51C4])
        for tt in range(tr.shape[0]):
            tr[tt, int(g.integers(tr.shape[1]))] = int(cap[4:])
        env._trace = tr
    elif cap.startswith('const'):
        env._trace = np.full_like(np.asarray(env._trace), int(cap[5:]))
    mus = delivery(order, hold, cap); prev = None; q = 0.0; recs = []
    for t in range(N_DEC):
        with no_oracle_access(env):
            mus(env, seed, load, t)
            views = env.transmit(); env.verify_mirror()
            mv = merge_views_v2(views, prev, t, env.action_interval, 'age'); prev = mv
            _, _, rec = env.step({i: int(topo[i].valid_phases[0]) for i in range(m)})
        q += float(rec['queue'])
        for i in range(m):
            ages = [int(round(float(e.age) / float(env.action_interval))) for e in mv[i].inbox]
            recs.append(dict(t=t, n_ent=len(ages), never=len(mv[i].neighbours) - len(ages), max_age=max(ages) if ages else -1,
                             b3=sum(max(a - 3, 0) for a in ages), n_stale=sum(a > 2 for a in ages), ages=ages, m1=len(mv[i].neighbours)))
    return q, recs


def summarise(allr):
    f = lambda k: np.array([r[k] for r in allr], float)
    ma = f('max_age'); ma = ma[ma >= 0]; F = float(np.mean([sum(a == 0 for a in r['ages']) for r in allr]))
    S = {tau: float(np.mean([sum(a > tau for a in r['ages']) for r in allr])) for tau in range(0, 15)}
    never = float(f('never').mean()); m1 = float(f('m1').mean())
    return dict(entries=float(f('n_ent').mean()), never=never, stale=float(f('n_stale').mean()), B3=float(f('b3').mean()),
                max_age_p50=float(np.percentile(ma, 50)), max_age_p95=float(np.percentile(ma, 95)), max_age_p99=float(np.percentile(ma, 99)),
                steps=len(allr), age_hist=np.bincount([x for r in allr for x in r['ages']], minlength=16).tolist(),
                B_tau={tau: float(np.mean([sum(max(x - tau, 0) for x in r['ages']) for r in allr])) for tau in range(0, 15)},
                F=F, S_tau=S, view=m1, net=F - S[2] - never, net_per_sender=(F - S[2] - never) / m1)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False); sc = Scenarios(out); res = {}
    for cell in a.cells:                                   # cell = order:hold:capacity
        order, hold, cap = cell.split(':'); allr = []
        for seed in a.traffic_seeds:
            for load in a.headways:
                _, rr = run(sc, seed, load, order, int(hold), cap); allr += rr
        res[cell] = summarise(allr)
        print(cell, ' '.join(f'{k} {v:.3f}' for k, v in res[cell].items() if isinstance(v, float)), flush=True)
    if a.selfcheck:
        ref = json.loads(Path(a.selfcheck).read_text())
        for K, cell in (('1', 'agefirst:1:const1'), ('2', 'agefirst:1:const2'), ('3', 'agefirst:1:const3'), ('0', 'agefirst:1:iid')):
            if cell not in res:
                continue
            for k in ('entries', 'never', 'stale', 'B3', 'age_hist'):
                if res[cell][k] != ref[K][k]:
                    raise SystemExit(f'SELF-CHECK FAIL: {cell} {k} {res[cell][k]} != v1 {ref[K][k]}')
        print('SELF-CHECK PASS: v2 reproduces v1 for the age-first const-K / iid cells present', flush=True)
    (out / 'composition.json').write_text(json.dumps(res, indent=1))
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS' if a.selfcheck else 'n/a', args=vars(a)), indent=1, default=str))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--cells', nargs='+', required=True, help='order:hold:capacity, e.g. agefirst:4:const2, countdeadline2:1:low')
    p.add_argument('--selfcheck', default=None, help="v1 composition.json to reproduce (agefirst:1:const<k> / iid cells)")
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=[901, 902, 903, 904]); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
