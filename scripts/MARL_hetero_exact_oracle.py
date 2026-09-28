#!/usr/bin/env python3
"""Exact oracle diagnostic for PROTOCOL_HETERO_v0 (one stream, heterogeneous receivers).

Written against research/marl_budget/PROTOCOL_HETERO_v0.md, which fixes the model, the
comparators, the preregistered snapshots and the decision rule BEFORE this script runs.
Replays the v2 episodes with the same live protocol; at each preregistered snapshot:
  * builds every receiver's action for EVERY subset of other senders (counterfactual views);
  * enumerates all m! base orders, de-duplicates joint actions, rolls out each distinct one;
  * prepares pi_adv on K_train only, evaluates on K_eval;
  * exact bounded-patch optimum (R = 0,1,2) from pi_adv and from the heuristic order, and the
    exact unrestricted private optimum, by enumerating products of achievable actions;
  * bytes of a canonical realisation of every reported profile.
Oracle-only; nothing here is deployable.  Values are held-phase rollout values (minus summed
waiting counts at H decision boundaries), not delay or unique vehicles.
"""
from __future__ import annotations
import argparse, gzip, hashlib, itertools, json, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from envs.external.cityflow_budgeted import BudgetTraceSpec, make_grid_scenario
from envs.external.cityflow_broadcast import make_broadcast_env
from models.marl_screening import no_oracle_access
from scripts.DIAG_cityflow_set_objective_hops import build_static, mp2_action
from scripts.MARL_cheap_screen import fingerprint, profile

DEPENDENCIES = ['scripts/MARL_hetero_exact_oracle.py', 'scripts/MARL_cheap_screen.py',
                'scripts/DIAG_cityflow_set_objective_hops.py', 'envs/external/cityflow_budgeted.py',
                'envs/external/cityflow_broadcast.py', 'models/marl_screening.py',
                'research/marl_budget/PROTOCOL_HETERO_v0.md']
CAP = 20000
PERMS = None


def source_hashes():
    return {n: hashlib.sha256((ROOT / n).read_bytes()).hexdigest() for n in DEPENDENCIES}


def popc(x):
    return bin(x).count('1')


class Snapshot:
    def __init__(self, env, actor, horizon):
        self.env, self.m, self.h = env, env.n_agents, horizon
        m = self.m
        # action of receiver i for every subset mask of OTHER senders
        self.act = [dict() for _ in range(m)]
        for i in range(m):
            others = [j for j in range(m) if j != i]
            for r in range(0, m):
                for S in itertools.combinations(others, r):
                    mask = sum(1 << j for j in S)
                    self.act[i][mask] = actor(i, env.counterfactual_view(i, list(S)))
        self.phases = [sorted(set(self.act[i].values())) for i in range(m)]
        self.aidx = [{p: n for n, p in enumerate(ph)} for ph in self.phases]
        self.base = max(len(p) for p in self.phases)
        self.cache = {}

    def value(self, joint):
        if joint not in self.cache:
            self.cache[joint] = self.env.oracle_rollout_value(dict(enumerate(joint)), self.h)
        return self.cache[joint]

    def prefix_masks(self, order, K):
        out = []
        for i in range(self.m):
            seq = [j for j in order if j != i][:K[i]]
            out.append(sum(1 << j for j in seq))
        return out

    def order_values(self, K):
        """Exact value of every order under capacity vector K (vectorised over m! orders)."""
        m = self.m; P = PERMS
        codes = np.zeros(len(P), dtype=np.int64)
        for i in range(m):
            wo = P[P != i].reshape(len(P), m - 1).astype(np.int64)
            masks = (1 << wo[:, :K[i]]).sum(1)
            lut = np.zeros(1 << m, dtype=np.int64)
            for mask, ph in self.act[i].items():
                lut[mask] = self.aidx[i][ph]
            codes = codes * self.base + lut[masks]
        uniq, inv = np.unique(codes, return_inverse=True)
        vals = np.empty(len(uniq))
        for n, c in enumerate(uniq):
            joint, x = [], int(c)
            digits = []
            for _ in range(m):
                digits.append(x % self.base); x //= self.base
            digits = digits[::-1]
            joint = tuple(self.phases[i][digits[i]] for i in range(m))
            vals[n] = self.value(joint)
        return vals[inv], len(uniq)

    def feasible(self, i, P_i, k, R):
        """{phase: canonical mask} over sets with |S|=k, |S\\P_i|<=R (R=None: unrestricted)."""
        others = [j for j in range(self.m) if j != i]
        best = {}
        for S in itertools.combinations(others, k):
            mask = sum(1 << j for j in S)
            r = popc(mask & ~P_i)
            if R is not None and r > R:
                continue
            ph = self.act[i][mask]
            key = (r, mask)
            if ph not in best or key < best[ph][0]:
                best[ph] = (key, mask)
        return {ph: v[1] for ph, v in best.items()}

    def best_profile(self, K, order, R):
        m = self.m
        P = self.prefix_masks(order, K) if order is not None else [0] * m
        feas = [self.feasible(i, P[i], K[i], R) for i in range(m)]
        size = int(np.prod([len(f) for f in feas]))
        if size > CAP:
            return None
        best_v, best_j = -float('inf'), None
        for joint in itertools.product(*[sorted(f) for f in feas]):
            v = self.value(tuple(joint))
            if v > best_v:
                best_v, best_j = v, joint
        sets = [feas[i][best_j[i]] for i in range(m)]
        return dict(value=best_v, joint=list(best_j), sets=sets, product=size,
                    bytes=self.bytes(order, K, P, sets, R))

    def bytes(self, order, K, P, sets, R):
        m = self.m
        if order is None:                       # private: union of sets + 2B per receiver
            T = 0
            for i, s in enumerate(sets):
                assert popc(s) == K[i] and not (s >> i) & 1
                T |= s
            return 25 * popc(T) + 2 * m
        pos = {j: n for n, j in enumerate(order)}
        L0 = max((max(pos[j] for j in range(m) if (P[i] >> j) & 1) + 1) if P[i] else 0 for i in range(m))
        T = sum(1 << j for j in order[:L0])
        repl = 0
        for i in range(m):
            T |= sets[i]; repl += popc(sets[i] & ~P[i])
        for i in range(m):                      # legality checks, audit §2.3
            assert popc(sets[i]) == K[i] and not (sets[i] >> i) & 1
            assert R is None or popc(sets[i] & ~P[i]) <= R
        return 25 * popc(T) + 3 * repl


def analyse(env, actor, horizon, rng, heur_order):
    m = env.n_agents
    snap = Snapshot(env, actor, horizon)
    K_train = [[int(x) for x in rng.integers(1, m - 1, size=m)] for _ in range(8)]
    K_eval = [[int(x) for x in rng.integers(1, m - 1, size=m)] for _ in range(8)]
    train_vals = [snap.order_values(K)[0] for K in K_train]
    adv_idx = int(np.argmax(np.mean(train_vals, axis=0)))
    adv = tuple(int(j) for j in PERMS[adv_idx])
    none = snap.value(tuple(snap.act[i][0] for i in range(m)))
    full = snap.value(tuple(snap.act[i][((1 << m) - 1) & ~(1 << i)] for i in range(m)))
    evals = []
    for K in K_eval:
        ov, n_uniq = snap.order_values(K)
        known = int(np.argmax(ov))
        rec = dict(K=K, known_shared=float(ov[known]), known_order=[int(j) for j in PERMS[known]],
                   n_distinct_shared_profiles=int(n_uniq))
        for name, order in (('adv', adv), ('heur', tuple(heur_order))):
            for R in (0, 1, 2):
                rec[f'{name}_R{R}'] = snap.best_profile(K, order, R)
        rec['private'] = snap.best_profile(K, None, None)
        pk = snap.prefix_masks(PERMS[known], K)
        rec['known_shared_bytes'] = snap.bytes(tuple(int(j) for j in PERMS[known]), K, pk, pk, 0)
        evals.append(rec)
    return dict(K_train=K_train, adv_order=list(adv), heur_order=list(heur_order), no_comm=none,
                full_comm=full, rollouts=len(snap.cache), evals=evals)


def run(a):
    global PERMS
    out = Path(a.out).resolve(); out.mkdir(parents=True, exist_ok=False)
    cfg = profile('pilot'); hashes = source_hashes()
    (out / 'manifest.json').write_text(json.dumps(dict(status='RUNNING', snapshots=a.snapshots,
                                                       source_hashes=hashes), indent=2))
    start = time.perf_counter(); n = 0
    seeds = cfg['seeds'][:a.max_episodes_seeds] if a.max_episodes_seeds else cfg['seeds']
    loads = cfg['loads'][:a.max_loads] if a.max_loads else cfg['loads']
    with gzip.open(out / 'records.jsonl.gz', 'wt') as raw:
        for seed, split in seeds:
            for load in loads:
                eid = f'seed{seed}_load{load:g}'
                horizon_n = max(a.snapshots) + 1
                scen = make_grid_scenario(out / 'scenarios' / eid, rows=cfg['rows'], cols=cfg['cols'],
                    traffic_seed=seed, horizon_s=10 * (cfg['warm'] + (cfg['snapshots'] - 1) * cfg['stride']
                                                       + 1 + cfg['horizon'] + 5), mean_headway_s=load)
                env = make_broadcast_env(scen, budget_spec=BudgetTraceSpec(kind='bursty',
                    k=cfg['rows'] * cfg['cols'] // 2, k_low=1),
                    n_decisions=cfg['warm'] + (cfg['snapshots'] - 1) * cfg['stride'] + 1, mode='oracle')
                env.reset(budget_seed=1000 + seed)
                if PERMS is None:
                    PERMS = np.array(list(itertools.permutations(range(env.n_agents))), dtype=np.int8)
                topo = {i: env.public_topology(i) for i in range(env.n_agents)}
                down, onward = build_static(topo)
                actor = lambda i, v: mp2_action(v, topo[i], down, onward)
                for t in range(horizon_n):
                    with no_oracle_access(env):
                        ctx = env.scheduler_context()
                        rot = t % env.n_agents
                        ranking = tuple(range(rot, env.n_agents)) + tuple(range(rot))
                        env.commit_global_ranking(ranking)
                        k = env.reveal_budget()
                    if t in a.snapshots:
                        before = fingerprint(env); t1 = time.perf_counter()
                        rng = np.random.default_rng(9000 + 100 * seed + int(load) + t)
                        res = analyse(env, actor, cfg['horizon'], rng, ctx.cached_queue_ranking())
                        if fingerprint(env) != before:
                            raise AssertionError('diagnostic changed the live state')
                        res.update(episode_id=eid, split=split, traffic_seed=seed, headway=load, t=t,
                                   seconds=time.perf_counter() - t1)
                        raw.write(json.dumps(res) + '\n'); raw.flush(); n += 1
                        print(f'{eid} t={t}: {res["rollouts"]} rollouts, {res["seconds"]:.0f}s; '
                              f'{n} records, {time.perf_counter() - start:.0f}s', flush=True)
                    with no_oracle_access(env):
                        env.submit_broadcast(ranking[:k])
                        views = env.transmit()
                        _, _, step = env.step({i: actor(i, v) for i, v in views.items()})
    if source_hashes() != hashes:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', snapshots=a.snapshots,
        source_hashes=hashes, records=n, cap=CAP,
        records_sha256=hashlib.sha256((out / 'records.jsonl.gz').read_bytes()).hexdigest(),
        evidence_class='EXACT ORACLE MECHANISM DIAGNOSTIC (PROTOCOL_HETERO_v0); frozen MP2; held-phase value',
        seconds=time.perf_counter() - start), indent=2))
    print('COMPLETE', out, n, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', required=True)
    p.add_argument('--snapshots', type=int, nargs='+', default=[19])
    p.add_argument('--max-episodes-seeds', type=int, default=0, help='smoke: first N traffic seeds')
    p.add_argument('--max-loads', type=int, default=0, help='smoke: first N loads')
    run(p.parse_args())
