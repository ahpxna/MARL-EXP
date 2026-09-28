#!/usr/bin/env python3
"""CLOSED-LOOP evaluation v4: the Where2comm-style request baseline on the DECLARED 1-byte bid only.

Correction of MARL_hetero_closed_loop_v3.py (kept unchanged; its where2comm_top2 rows stay as
historical evidence, labelled "leaks exact gap").  v3 sorted the fragile receivers by the EXACT local
MP2 gap, which the 1-byte bid (p1, p2, gapbin) does not transmit: two gaps in one bin cannot be
ordered by the scheduler.  Independent recheck, 27/09 (MARL_CRITICAL_PATH_INDEPENDENT_RECHECK).

  where2comm_top2_bin   identical to v3's where2comm_top2 except that the scheduler sees only the
                        transmitted gapbin: fragile = gapbin <= 1 (equivalent to gap < 2, asserted),
                        processed in the order (gapbin, receiver id) -- a public deterministic tie
                        rule.  Everything else (p1, p2 from the bid; |c_ij| * staleness_ij from the
                        public topology, known MP2 and mirror ages; swap rule; byte cap; 10 B bid
                        charged) is unchanged.
prefix is re-run in the same producer as the pairing anchor.  Deployable rows run inside
no_oracle_access except the receiver-side bid computation (own view only), as in v3.
"""
from __future__ import annotations
import argparse, hashlib, json, os, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets, profile_cost
from scripts.DIAG_cityflow_set_objective_hops import mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_hetero_response_replay import checked, gap_of
from scripts.MARL_hetero_bid_replay import coefficients
from scripts.MARL_hetero_bid_replay_v2 import gapbin
from scripts.MARL_hetero_closed_loop import make_env
import scripts.MARL_hetero_closed_loop_v3 as v3

SOURCES = ['scripts/MARL_hetero_closed_loop_v4.py', 'scripts/MARL_hetero_closed_loop_v3.py',
           'scripts/MARL_hetero_closed_loop_v2.py', 'scripts/MARL_hetero_closed_loop.py',
           'scripts/MARL_hetero_bid_replay_v2.py']
BIDB = 10


def where2comm_bin_episode(out, seed, load, cap):
    method = 'where2comm_top2_bin'
    eid, env, topo, down, onward = make_env(out, seed, load, method)
    coef = {i: coefficients(topo[i], down, onward) for i in range(env.n_agents)}
    m = env.n_agents; total = 0; edits = 0
    for t in range(N_DEC):
        with no_oracle_access(env):
            ctx = env.scheduler_context(); order = tuple(ctx.cached_queue_ranking())
            env.commit_global_ranking(order); Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
        P = prefix_sets(order, K); sets = [set(s) for s in P]
        now = env._now(); info = []
        for i in range(m):
            v = env._build_view(i); _, sc = checked(v, topo[i], down, onward)      # receiver side
            o = sorted(sc, key=lambda p: -sc[p]); p1, p2 = o[0], o[1]; g = gap_of(sc); gb = gapbin(g)
            assert (gb <= 1) == (g < 2)
            # ---- scheduler side from here: only (p1, p2, gb) of receiver i ----
            imp = {}
            for j in range(m):
                if j == i:
                    continue
                cj = abs(coef[i][p1].get(j, 0.0) - coef[i][p2].get(j, 0.0))
                e = env.mirror.entry(i, j); st = 10.0 if e is None else 1.0 + float(now - e[1]) / 10.0
                imp[j] = cj * st
            info.append((gb, i, imp))
        b0 = profile_cost(order, K, sets)[0]
        for gb, i, imp in sorted(info, key=lambda x: (x[0], x[1])):
            if gb > 1:
                break
            out_c = [j for j in imp if j not in sets[i] and imp[j] > 0]
            if not out_c or not sets[i]:
                continue
            add = max(out_c, key=lambda j: imp[j]); drop = min(sets[i], key=lambda j: imp.get(j, 0.0))
            if imp[add] <= imp.get(drop, 0.0):
                continue
            trial = [set(s) for s in sets]; trial[i] = (trial[i] - {drop}) | {add}
            if profile_cost(order, K, trial)[0] <= b0 + cap - BIDB:
                sets = trial; edits += 1
        with no_oracle_access(env):
            env.submit_profile(sets, R=None, cap=profile_cost(order, K, [set(s) for s in P])[0] + cap)
            views = env.transmit(); env.verify_mirror()
            _, _, rec = env.step({i: mp2_action(v, topo[i], down, onward) for i, v in views.items()})
            total += rec['accounted_bytes'] + BIDB
    return dict(episode=eid, method=method, queue_sum=float(sum(r['queue'] for r in env.step_records)),
                finished=int(env.step_records[-1]['finished']), bytes=int(total), edits=edits, summary=env.episode_summary())


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    rows = []; t0 = time.perf_counter()
    for seed in a.traffic_seeds:
        for load in (8.0, 16.0):
            for meth in ('prefix', 'where2comm_top2_bin'):
                r = (v3.v2.episode(out, seed, load, 'prefix', None, a.cap, 'direct', None) if meth == 'prefix'
                     else where2comm_bin_episode(out, seed, load, a.cap))
                rows.append(r)
                print(f'[{time.perf_counter() - t0:.0f}s] {r["episode"]} {meth}: queue_sum {r["queue_sum"]:.0f} '
                      f'finished {r["finished"]} bytes {r["bytes"]} edits {r["edits"]}', flush=True)
                tmp = out / '.rows.json'; tmp.write_text(json.dumps(rows, default=float)); os.replace(tmp, out / 'rows.json')
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), source_hashes=h0,
        seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True); p.add_argument('--traffic-seeds', type=int, nargs='+', required=True)
    p.add_argument('--cap', type=int, default=84)
    main(p.parse_args())
