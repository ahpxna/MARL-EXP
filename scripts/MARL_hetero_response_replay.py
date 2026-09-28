#!/usr/bin/env python3
"""Mitigation M-A/M-B inputs: a LEGAL actor-response model and RECEIVER-LOCAL bid quantities.

Deterministic replay of labelled hetero episodes (same trajectory and checks as
MARL_hetero_mirror_replay.py) that adds, at every labelled snapshot and for every labelled
profile:

  pjoint   LEGAL predicted joint MP2 action.  The actor is the system's own frozen controller
           (its code is known to the scheduler).  For receiver i and set S_i the scheduler builds
           the view MP2 reads from what it legally knows:
             own per-slot waiting  <- its cached copy of i's own last broadcast packet
             sender j in S_i       <- its latest broadcast copy of j (the fresh payload is unknown)
             sender j not in S_i   <- receiver i's own cached copy, from the receiver mirror
           Built with _summary/_sensor disabled.  No counterfactual view, no oracle call.
  lgapP    LEGAL MP2 score gap (best - second best) of every receiver under the prefix.
  bid      RECEIVER-SIDE quantities a receiver can compute locally BEFORE transmission from its
           own sensor and its own cache (no other fresh payload): preferred action, score gap,
           own per-slot waiting.  They reach the scheduler only through a charged bid.

Checks (abort on failure): z / order / K reproduce the labels; the local MP2 score function
reproduces mp2_action on every view it scores; mirror == receiver caches after every transmit.
The TRUE counterfactual joint actions are already in the mirror replay (privileged); here they
are only compared, never used.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from envs.external.cityflow_budgeted import BudgetTraceSpec, make_grid_scenario, N_SLOTS
from envs.external.cityflow_hetero_mirror import make_hetero_mirror_env
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from scripts.DIAG_cityflow_set_objective_hops import build_static, mp2_action, LAMBDA
from scripts.MARL_hetero_pilot_collect import N_DEC, H, ROWS, COLS

SOURCES = ['scripts/MARL_hetero_response_replay.py', 'envs/external/cityflow_hetero_mirror.py',
           'envs/external/cityflow_hetero.py', 'models/marl_receiver_mirror.py',
           'scripts/MARL_hetero_pilot_collect.py', 'scripts/DIAG_cityflow_set_objective_hops.py']


def unmask(x):
    return [j for j in range(16) if (x >> j) & 1]


class _E:
    __slots__ = ('payload',)

    def __init__(self, p):
        self.payload = p


class LegalView:
    """The two fields mp2_action reads, built from legal knowledge only."""

    def __init__(self, own_slots, entries):
        self.lane_waiting = np.asarray(own_slots, float)[:, None]      # sum(axis=1) = slot totals
        self._e = entries

    def message_from(self, j):
        p = self._e.get(j)
        return None if p is None else _E(p)


def mp2_scores(view, topo, down, onward):
    """Phase values exactly as mp2_action computes them."""
    wait = np.asarray(view.lane_waiting).sum(axis=1)

    def heard(j, s):
        e = view.message_from(j)
        return float(e.payload.waiting[s]) if e is not None else 0.0
    out = {}
    i = topo.agent
    for p in topo.valid_phases:
        val = 0.0
        for (s, road) in topo.phase_movements[p]:
            up = float(wait[s]); j, sj = down[i].get(road, (None, None)); dn1 = dn2 = 0.0
            if j is not None:
                dn1 = heard(j, sj); nxt = onward.get(j, {}).get(sj, [])
                if nxt:
                    dn2 = float(np.mean([heard(j2, s2) for (j2, s2) in nxt]))
            val += up - dn1 - LAMBDA * dn2
        out[p] = val
    return out


def gap_of(scores):
    v = sorted(scores.values(), reverse=True)
    return float(v[0] - v[1]) if len(v) > 1 else 1e9


def checked(view, topo, down, onward):
    sc = mp2_scores(view, topo, down, onward)
    a = mp2_action(view, topo, down, onward)
    best = None
    for p in topo.valid_phases:                                       # same tie rule as mp2_action
        if best is None or sc[p] > sc[best] + 1e-12:
            best = p
    if int(best) != int(a):
        raise AssertionError('mp2_scores disagrees with mp2_action')
    return a, sc


def run(a):
    shards = [Path(x) for x in a.labels]
    out = Path(a.out).resolve(); out.mkdir(parents=True, exist_ok=False)
    hashes = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    start = time.perf_counter(); n = 0
    with gzip.open(out / 'response_diag.jsonl.gz', 'wt') as raw:
        for labels_dir in shards:
            man = json.loads((labels_dir / 'manifest.json').read_text())
            if hashlib.sha256((labels_dir / 'labels.jsonl.gz').read_bytes()).hexdigest() != man['labels_sha256']:
                raise ValueError('labels hash mismatch')
            by_ep = {}
            for l in gzip.open(labels_dir / 'labels.jsonl.gz', 'rt'):
                r = json.loads(l); by_ep.setdefault((r['traffic_seed'], r['headway']), {})[r['t']] = r
            for (seed, load), snaps in sorted(by_ep.items()):
                eid = f'seed{seed}_load{load:g}'
                scen = make_grid_scenario(out / 'scenarios' / eid, rows=ROWS, cols=COLS, traffic_seed=seed,
                                          horizon_s=10 * (N_DEC + H + 5), mean_headway_s=load)
                env = make_hetero_mirror_env(scen, budget_spec=BudgetTraceSpec(kind='bursty', k=4, k_low=1),
                                             n_decisions=N_DEC, capacity_seed=5000 + 10 * seed + int(load),
                                             mode='oracle')
                env.reset(budget_seed=1000 + seed)
                topo = {i: env.public_topology(i) for i in range(env.n_agents)}
                down, onward = build_static(topo)
                m = env.n_agents
                for t in range(max(snaps) + 1):
                    with no_oracle_access(env):
                        ctx = env.scheduler_context()
                        z = ctx.features(); order = tuple(ctx.cached_queue_ranking())
                        env.commit_global_ranking(order)
                        Kd = env.reveal_budget(); K = [int(Kd[i]) for i in range(m)]
                    if t in snaps:
                        lab = snaps[t]
                        if lab['z'] != z or tuple(lab['order']) != order or lab['groups'][0]['K'] != K:
                            raise AssertionError(f'{eid} t={t}: replay does not reproduce the labelled snapshot')
                        pk = ctx.packets
                        with no_oracle_access(env):
                            def forbid(*_, **__):
                                raise AssertionError('fresh sensor read in the legal response model')
                            env._summary = env._sensor = forbid
                            try:
                                own = [list(pk[i].waiting) if pk[i] is not None else [0] * N_SLOTS for i in range(m)]
                                memo = {}

                                def pact(i, mask):
                                    if (i, mask) not in memo:
                                        S = set(unmask(mask)); ent = {}
                                        for j in env.neighbours[i]:
                                            if j in S:
                                                ent[j] = pk[j]
                                            else:
                                                e = env.mirror.entry(i, j)
                                                ent[j] = None if e is None else e[0]
                                        memo[(i, mask)] = checked(LegalView(own[i], ent), topo[i], down, onward)
                                    return memo[(i, mask)]
                                pjoint = [[[int(pact(i, pm[i])[0]) for i in range(m)] for pm in g['profiles']]
                                          for g in lab['groups']]
                                lgapP = []
                                for g in lab['groups']:
                                    Pm = [sum(1 << j for j in s) for s in prefix_sets(order, g['K'])]
                                    lgapP.append([gap_of(pact(i, Pm[i])[1]) for i in range(m)])
                            finally:
                                del env._summary, env._sensor
                        # receiver-side, before transmission: own sensor + own cache only
                        bid = []
                        for i in range(m):
                            v = env._build_view(i)
                            if v.inbox:
                                raise AssertionError('receiver view has an inbox before transmission')
                            act, sc = checked(v, topo[i], down, onward)
                            bid.append(dict(pref=int(act), gap=gap_of(sc),
                                            own=[float(x) for x in np.asarray(v.lane_waiting).sum(axis=1)]))
                        raw.write(json.dumps(dict(episode_id=eid, split=lab['split'], traffic_seed=seed,
                                                  headway=load, t=t, pjoint=pjoint, lgapP=lgapP, bid=bid)) + '\n')
                        raw.flush(); n += 1
                        print(f'{lab["split"]} {eid} t={t}: {len(memo)} legal actions; {n} records, '
                              f'{time.perf_counter() - start:.0f}s', flush=True)
                    with no_oracle_access(env):
                        env.submit_profile(prefix_sets(order, K), R=0)
                        views = env.transmit()
                        env.verify_mirror()
                        env.step({i: mp2_action(v, topo[i], down, onward) for i, v in views.items()})
    if hashes != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during replay')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', records=n,
        labels=[str(s.resolve()) for s in shards], source_hashes=hashes,
        response_sha256=hashlib.sha256((out / 'response_diag.jsonl.gz').read_bytes()).hexdigest(),
        pjoint='LEGAL: frozen MP2 on scheduler-known data (own/heard <- scheduler cache, others <- mirror)',
        bid='RECEIVER-SIDE local quantities; usable by the scheduler only through a charged bid',
        seconds=time.perf_counter() - start), indent=2))
    print('COMPLETE', out, n, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--labels', nargs='+', required=True); p.add_argument('--out', required=True)
    run(p.parse_args())
