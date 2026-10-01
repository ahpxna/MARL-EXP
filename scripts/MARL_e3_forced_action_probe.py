#!/usr/bin/env python3
"""Is the E3 scheduling headroom an INFORMATION effect or an ACTION-PERTURBATION effect?  (29/09; oracle diagnostic;
no learner, no selector)

The stored labels show: a candidate's 3-step gain is mostly set by the joint action it induces at t (within-joint-group
variance 19-26% of the total); half of the candidates induce the prefix joint action; the best candidate changes 1.3-2.3
agents' actions; random candidates average about 0.  That pattern is also what best-of-N selection over zero-mean
perturbations of a good but imperfect actor would give.  Control: at the same DEV states, keep the PREFIX delivery and
FORCE one agent's action at step t to each other valid phase (no message changes), then run the prefix for t+1, t+2 and
score -sum(queue) exactly like the stored label.  Compared per state with the stored message candidates (feasible
+74 B): the oracle, the mean, the share positive, and a matched-N best-of (N = the number of distinct joint actions the
message candidates induce; random subsets of the forced perturbations, averaged).  Paired: for message candidates that
change exactly ONE agent's action, the stored gain vs the forced gain of the same (agent, action) = the part carried by
the delivered message beyond the action at t.
Self-checks (abort): the replayed state at t equals the stored one; forcing an agent to its own prefix action
reproduces the stored prefix cont exactly.  Evidence class: oracle diagnostic.
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
from scripts.MARL_hetero_pilot_collect import H
from scripts.MARL_e3_continuation_labels import Policy, step_with
from scripts.MARL_e3_selector_train import load
from scripts.MARL_e3_hindsight_probe import OneScenario, base_until

SOURCES = ['scripts/MARL_e3_forced_action_probe.py', 'scripts/MARL_e3_hindsight_probe.py', 'scripts/MARL_e3_continuation_labels.py',
           'scripts/MARL_hetero_target_diag.py', 'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']


def forced_cont(sc, seed, load_, pol, t, agent, action):
    """Prefix for steps < t; at t the prefix delivery with agent's action forced; prefix for t+1..t+H-1; -sum(queue)."""
    env, _, _, _ = sc.env(seed, load_)
    for _ in range(t):
        with no_oracle_access(env):
            order, K = grant(env)
        step_with(env, pol, prefix_sets(order, K))
    with no_oracle_access(env):
        order, K = grant(env)
        env.submit_profile([set(s) for s in prefix_sets(order, K)], R=None)
        views = env.transmit(); env.verify_mirror()
        bad = env.check_access_invariants(views)
        if bad:
            raise AssertionError(f'access invariant: {bad[:3]}')
        acts = pol.act(views); own = acts[agent]; acts[agent] = int(action)
        _, _, rec = env.step(acts)
    q = [float(rec['queue'])]
    for _ in range(H - 1):
        with no_oracle_access(env):
            o, k = grant(env)
        q.append(step_with(env, pol, prefix_sets(o, k))[0])
    return -float(sum(q)), own


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
        env0, topo, _, _ = so.env(seed, load_); pol = Policy(ckp, topo, env0.action_interval); mask = pol.adapter.valid_mask()
        for st in sorted(by_ep[(seed, load_)], key=lambda s: s['t'])[:a.limit_states or None]:
            t = st['t']; c0 = st['cands'][0]['cont']; j0 = list(st['cands'][0]['joint'])
            _, o_ref, k_ref, z_ref = base_until(so, seed, load_, pol, t)
            if o_ref != st['order'] or k_ref != st['K'] or max(abs(x - y) for x, y in zip(z_ref, st['z'])) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: replay does not reproduce the stored state {seed}/{load_}/t{t}')
            v, own = forced_cont(so, seed, load_, pol, t, 0, j0[0])
            if abs(v - c0) > 1e-9 or own != j0[0]:
                raise SystemExit(f'SELF-CHECK FAIL: {seed}/{load_}/t{t}: forcing the own action does not reproduce the prefix cont ({v} vs {c0})')
            forced = []
            for i in range(st['m']):
                for ph in np.where(mask[i])[0]:
                    if int(ph) != j0[i]:
                        forced.append(dict(agent=i, action=int(ph), gain=forced_cont(so, seed, load_, pol, t, i, int(ph))[0] - c0))
            ok = [k for k, c in enumerate(st['cands']) if k == 0 or c['bytes'] <= st['b0'] + 74]
            msg = [dict(gain=st['cands'][k]['cont'] - c0, joint=list(st['cands'][k]['joint'])) for k in ok[1:]]
            rows.append(dict(episode=f'seed{seed}_load{load_:g}', t=t, prefix_joint=j0, forced=forced, message=msg))
            fg = np.array([f['gain'] for f in forced]); mg = np.array([m_['gain'] for m_ in msg])
            print(f'[{time.perf_counter() - t0:.0f}s] seed{seed}_load{load_:g} t{t}: forced n {len(fg)} max {fg.max():+.1f} mean {fg.mean():+.2f} | '
                  f'message n {len(mg)} max {mg.max():+.1f} mean {mg.mean():+.2f}', flush=True)
            (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), states=len(rows), H=H,
                                                       source_hashes=h0, seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor-dir', required=True); p.add_argument('--shard', type=int, default=0); p.add_argument('--nshards', type=int, default=1)
    p.add_argument('--limit-states', type=int, default=0, help='smoke only: states per episode'); p.add_argument('--out', required=True)
    main(p.parse_args())
