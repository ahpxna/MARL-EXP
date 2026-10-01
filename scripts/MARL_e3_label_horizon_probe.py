#!/usr/bin/env python3
"""Does the 3-step continuation label predict the FULL-EPISODE effect of an edit?  (auditor's test 3; diagnostic;
oracle labels only; no learner, no selector, no normaliser)

The E3 label cont_3(S) of a DEV state is: profile S at step t, then the committed prefix at t+1, t+2 (H = 3), score
-sum(queue).  The closed loop is scored on the queue sum of all N_DEC = 26 steps.  This probe replays the SAME candidate
subset as MARL_e3_hindsight_probe.py (the prefix, the stored oracle-best feasible candidate (+84 B - 10 B bid), and
--cands random feasible others, same seeded draw) with profile S at t and the prefix at EVERY later step to the end of
the episode (a single edit, then the prefix: what the guarded closed loop mostly does), on the original traffic.
Recorded per candidate: the queue at every step t..N_DEC-1.  g3 = the 3-step gain vs the prefix (= the stored label
difference), g_full = the gain on the closed-loop metric (steps t..N_DEC-1; earlier steps are identical), g_rest =
g_full - g3.  Self-checks (abort): the recomputed state at t equals the stored one; for every candidate the first H
steps reproduce the stored cont exactly; the prefix row reproduces a plain prefix episode.
Evidence class: oracle diagnostic.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from collections import defaultdict
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from scripts.MARL_hetero_target_diag import grant, scenario
from scripts.MARL_hetero_pilot_collect import H, N_DEC
from scripts.MARL_e3_continuation_labels import Policy, step_with
from scripts.MARL_e3_selector_train import load
from scripts.MARL_e3_hindsight_probe import OneScenario, base_until

SOURCES = ['scripts/MARL_e3_label_horizon_probe.py', 'scripts/MARL_e3_hindsight_probe.py', 'scripts/MARL_e3_continuation_labels.py',
           'scripts/MARL_hetero_target_diag.py', 'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']


def replay_full(sc, seed, load_, pol, t, S):
    """Prefix for steps < t, profile S at t, prefix at every later step; queues of steps t..N_DEC-1."""
    env, _, _, _ = sc.env(seed, load_)
    for _ in range(t):
        with no_oracle_access(env):
            order, K = grant(env)
        step_with(env, pol, prefix_sets(order, K))
    with no_oracle_access(env):
        grant(env)
    q = [step_with(env, pol, S)[0]]
    for _ in range(N_DEC - t - 1):
        with no_oracle_access(env):
            o, k = grant(env)
        q.append(step_with(env, pol, prefix_sets(o, k))[0])
    return q


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    D = Path(a.actor_dir); S, ck = load([D / 'labels_dev']); ckp = torch.load(ck.pop(), weights_only=False)
    by_ep = defaultdict(list)
    for st in S:
        by_ep[(st['traffic_seed'], st['headway'])].append(st)
    eps = sorted(by_ep)[a.shard::a.nshards]; rows = []; t0 = time.perf_counter()
    for seed, load_ in eps:
        orig = scenario(out / 'orig', seed, load_); so = OneScenario(orig)
        env0, topo, _, _ = so.env(seed, load_); pol = Policy(ckp, topo, env0.action_interval)
        q_pre_ep = None
        for st in sorted(by_ep[(seed, load_)], key=lambda s: s['t']):
            t = st['t']
            ok = [i for i, c in enumerate(st['cands']) if i == 0 or c['bytes'] <= st['b0'] + 74]
            best = max(ok, key=lambda i: st['cands'][i]['cont'])
            rng = np.random.default_rng([seed, int(load_), t, 7])
            others = [i for i in ok if i not in (0, best)]; pick = [0, best] + sorted(rng.choice(others, size=min(a.cands, len(others)), replace=False).tolist())
            q_ref, o_ref, k_ref, z_ref = base_until(so, seed, load_, pol, t)
            if o_ref != st['order'] or k_ref != st['K'] or max(abs(x - y) for x, y in zip(z_ref, st['z'])) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: replay does not reproduce the stored state {seed}/{load_}/t{t}')
            Q = []
            for i in pick:
                q = replay_full(so, seed, load_, pol, t, [set(s) for s in st['cands'][i]['sets']])
                if abs(-float(sum(q[:H])) - st['cands'][i]['cont']) > 1e-9:
                    raise SystemExit(f'SELF-CHECK FAIL: {seed}/{load_}/t{t}/c{i}: first {H} steps {-sum(q[:H])} != stored cont {st["cands"][i]["cont"]}')
                Q.append(q)
            full_pre = q_ref + Q[0]
            if q_pre_ep is None:
                q_pre_ep = full_pre
            elif q_pre_ep != full_pre:
                raise SystemExit(f'SELF-CHECK FAIL: {seed}/{load_}: the prefix episode differs between snapshots')
            Q = np.array(Q); g3 = -(Q[:, :H].sum(1) - Q[0, :H].sum()); gf = -(Q.sum(1) - Q[0].sum())
            rows.append(dict(episode=f'seed{seed}_load{load_:g}', t=t, picked=pick, stored_best=best, queues=Q.tolist(),
                             prefix_episode_queue_sum=float(sum(full_pre))))
            print(f'[{time.perf_counter() - t0:.0f}s] seed{seed}_load{load_:g} t{t}: stored-best g3 {g3[1]:.1f} g_full {gf[1]:.1f} | '
                  f'best by g_full {gf.max():.1f} (g3 {g3[int(gf.argmax())]:.1f}) | prefix episode queue sum {sum(full_pre):.0f}', flush=True)
            (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), states=len(rows), H=H, N_DEC=N_DEC,
                                                       source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor-dir', required=True); p.add_argument('--cands', type=int, default=15)
    p.add_argument('--shard', type=int, default=0); p.add_argument('--nshards', type=int, default=1); p.add_argument('--out', required=True)
    main(p.parse_args())
