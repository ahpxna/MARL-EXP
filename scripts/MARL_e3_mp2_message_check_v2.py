#!/usr/bin/env python3
"""v2 (29/09 19:4x) of MARL_e3_mp2_message_check.py (unchanged; its results are L-114): a candidate FIX of the reference
controller.  L-114 found MP2 14 % worse with messages than the same rule without its downstream terms.  MASTER's
contaminated-anchor reading: downstream WAITING counts move with the downstream intersection's own signal phase.  Variants
(1-hop unless noted), upstream term as in MP2 (approach-total waiting per movement):
  mp_veh      downstream VEHICLE counts instead of waiting (payload.vehicles[s_j])
  mp_veh2     the same with the 2-hop term (LAMBDA = 0.5), i.e. MP2 with vehicles
  mp_vehup    upstream VEHICLES and downstream vehicles (occupancy pressure)
  maxq        no downstream terms (L-114's best), and maxq_veh: upstream vehicles, no downstream terms
under the prefix and full deliveries (and none, where the downstream terms vanish).  128 episodes, seeds 901-964 x 8/16.
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


def heard(view, j, s, field):
    e = view.message_from(j)
    return float(getattr(e.payload, field)[s]) if e is not None else 0.0


def act(kind, view, topo, down, onward):
    if kind == 'mp2':
        return mp2_action(view, topo, down, onward)
    up_field = 'lane_vehicles' if kind in ('mp_vehup', 'maxq_veh') else 'lane_waiting'
    up = np.asarray(getattr(view, up_field)).sum(axis=1); i = topo.agent; best, bv = None, None
    for p in topo.valid_phases:
        val = 0.0
        for (s, road) in topo.phase_movements[p]:
            val += float(up[s])
            if kind in ('maxq', 'maxq_veh'):
                continue
            j, sj = down[i].get(road, (None, None))
            if j is None:
                continue
            val -= heard(view, j, sj, 'vehicles')
            if kind == 'mp_veh2':
                nxt = onward.get(j, {}).get(sj, [])
                if nxt:
                    val -= LAMBDA * float(np.mean([heard(view, j2, s2, 'vehicles') for (j2, s2) in nxt]))
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
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), LAMBDA=LAMBDA), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--out', required=True); p.add_argument('--kinds', nargs='+', default=['mp_veh', 'mp_veh2', 'mp_vehup', 'maxq', 'maxq_veh'])
    p.add_argument('--deliveries', nargs='+', default=['prefix', 'full'])
    p.add_argument('--traffic-seeds', type=int, nargs='+', default=list(range(901, 965))); p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    main(p.parse_args())
