#!/usr/bin/env python3
"""Does the MP2 reference controller USE messages well?  (29/09 19:4x; audit of the fixed-MP2 track's actor)

The E3 trainers' select logs show MP2's reference waiting at 1474 with no deliveries and 1730-1766 with prefix or FULL
deliveries.  A max-pressure controller given fresh downstream queues should not be much worse than without them, so
this checks, on the closed-loop panel episodes, MP2 as implemented (scripts/DIAG_cityflow_set_objective_hops.mp2_action:
per movement, approach-total upstream waiting - downstream approach waiting - LAMBDA * mean 2-hop waiting) and variants:
  mp2        as implemented (LAMBDA = 0.5)
  mp1        LAMBDA = 0 (1-hop pressure)
  maxq       downstream terms dropped (max total upstream queue over the phase's movements, as mp2 with no messages)
  mp1_dedup  1-hop pressure with each incoming approach counted ONCE per phase (upstream approach waiting minus the
             mean downstream waiting of that approach's movements in the phase)
under delivery rules prefix / full / none (MARL_e3_actor_train_delivery_v5.deliver).  Metric: sum of queues per episode
(the closed-loop metric), mean over episodes, and each rule's paired change against mp2/prefix.
"""
from __future__ import annotations
import argparse, json, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_e3_actor_train import Scenarios
import scripts.MARL_e3_actor_train_delivery_v5 as DV
from scripts.DIAG_cityflow_set_objective_hops import mp2_action, LAMBDA


def heard(view, j, s):
    e = view.message_from(j)
    return float(e.payload.waiting[s]) if e is not None else 0.0


def act(kind, view, topo, down, onward):
    if kind == 'mp2':
        return mp2_action(view, topo, down, onward)
    wait = np.asarray(view.lane_waiting).sum(axis=1); i = topo.agent; best, bv = None, None
    for p in topo.valid_phases:
        mv = topo.phase_movements[p]; val = 0.0
        if kind == 'maxq':
            val = sum(float(wait[s]) for (s, _) in mv)
        elif kind == 'mp1':
            for (s, road) in mv:
                j, sj = down[i].get(road, (None, None)); val += float(wait[s]) - (heard(view, j, sj) if j is not None else 0.0)
        elif kind == 'mp1_dedup':
            by = {}
            for (s, road) in mv:
                j, sj = down[i].get(road, (None, None)); by.setdefault(s, []).append(heard(view, j, sj) if j is not None else 0.0)
            val = sum(float(wait[s]) - float(np.mean(d)) for s, d in by.items())
        else:
            raise ValueError(kind)
        if bv is None or val > bv + 1e-12:
            best, bv = p, val
    return int(best)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False); sc = Scenarios(out); rows = []; t0 = time.perf_counter()
    for kind in a.kinds:
        for rule in a.deliveries:
            for seed in a.traffic_seeds:
                for load in a.headways:
                    env, topo, down, onward = sc.env(seed, load); DV.DELIVERY['mode'] = rule; q = 0.0
                    for t in range(N_DEC):
                        with no_oracle_access(env):
                            DV.deliver(env, seed, load, t); views = env.transmit()
                            acts = {i: act(kind, v, topo[i], down, onward) for i, v in views.items()}
                            _, _, rec = env.step(acts)
                        q += float(rec['queue'])
                    rows.append(dict(kind=kind, rule=rule, episode=f'seed{seed}_load{load:g}', queue_sum=q))
            print(f'[{time.perf_counter() - t0:.0f}s] {kind} {rule}: mean waiting {np.mean([r["queue_sum"] for r in rows if r["kind"] == kind and r["rule"] == rule]):.1f}', flush=True)
    (out / 'rows.json').write_text(json.dumps(rows))
    ref = {r['episode']: r['queue_sum'] for r in rows if r['kind'] == 'mp2' and r['rule'] == 'prefix'}
    if ref:
        for kind in a.kinds:
            for rule in a.deliveries:
                d = [r['queue_sum'] / ref[r['episode']] - 1 for r in rows if r['kind'] == kind and r['rule'] == rule]
                print(f'{kind:10s} {rule:7s} vs mp2/prefix {np.mean(d):+.4f} (sd {np.std(d):.4f}, n {len(d)})')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), LAMBDA=LAMBDA), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--out', required=True); p.add_argument('--kinds', nargs='+', default=['mp2', 'mp1', 'maxq', 'mp1_dedup'])
    p.add_argument('--deliveries', nargs='+', default=['prefix', 'full', 'none'])
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=list(range(901, 965))); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    main(p.parse_args())
