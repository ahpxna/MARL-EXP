#!/usr/bin/env python3
"""E3 message-use check for a FROZEN actor checkpoint (readiness audit P2.4).

Same actor, same development episodes (default 501-508 x headways 8, 16; opened split), same
prefix scheduler and capacity trace; only what the actor is allowed to read changes:
  actual   the delivered view;
  full     every receiver decodes every other sender (capacity trace set to m-1; reference);
  none     all messages removed from the actor input;
  stale    this step's deliveries removed, last step's messages kept with age + interval;
  shuffle  payloads permuted among heard senders (identity broken, content kept).
References on the same episodes: frozen MP2 with the delivered view, and MP2 with full delivery.
Reported: closed-loop sum of waiting per variant, paired relative change against 'actual' with a
bootstrap over episodes; and, along the ACTUAL trajectory, the input-level action-change rate of
each transformation (same state, greedy actions).
Self-checks (abort): env.check_access_invariants on every step; for every receiver and every sender
neither delivered now nor cached, the actor-input block equals the missing encoding (the actor
cannot read an undelivered payload); mirror == caches after every transmission.
"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from models.marl_comm_actor import CommAdapter, ActorNet
from scripts.DIAG_cityflow_set_objective_hops import mp2_action
from scripts.MARL_hetero_pilot_collect import N_DEC
from scripts.MARL_hetero_target_diag import grant
from scripts.MARL_e3_actor_train import Scenarios

SOURCES = ['scripts/MARL_e3_message_use.py', 'scripts/MARL_e3_actor_train.py', 'models/marl_comm_actor.py',
           'envs/external/cityflow_hetero.py', 'envs/external/cityflow_budgeted.py']
VARIANTS = ['actual', 'none', 'stale', 'shuffle']


def run(sc, seed, load, policy, variant, actor, adapter, mask, full=False, probe=False, rng=None):
    env, topo, down, onward = sc.env(seed, load); m = env.n_agents
    if full:
        env._trace = np.full((env.n_decisions, m), m - 1, dtype=np.int64)
    adapter.reset(); q = []; changes = {v: [] for v in VARIANTS[1:]}; missing_checked = 0
    miss = None
    for t in range(N_DEC):
        with no_oracle_access(env):
            order, K = grant(env)
            env.submit_profile(prefix_sets(order, K), R=0)
            views = env.transmit(); env.verify_mirror()
            bad = env.check_access_invariants(views)
            if bad:
                raise AssertionError(f'access invariant: {bad[:3]}')
            if policy == 'mp2':
                acts = {i: mp2_action(v, topo[i], down, onward) for i, v in views.items()}
            else:
                X = np.stack([adapter.encode(views[i], variant, rng) for i in range(m)])
                with torch.no_grad():
                    A = actor(torch.as_tensor(X), mask).argmax(-1).numpy()
                acts = {i: int(A[i]) for i in range(m)}
                if probe:
                    for v in VARIANTS[1:]:
                        Xv = np.stack([adapter.encode(views[i], v, rng) for i in range(m)])
                        with torch.no_grad():
                            Av = actor(torch.as_tensor(Xv), mask).argmax(-1).numpy()
                        changes[v].append(float((Av != A).mean()))
                    for i in range(m):                     # undelivered payloads must be unreadable
                        heard = {e.sender for e in views[i].inbox} | {e.sender for e in views[i].cache}
                        x = adapter.encode(views[i], 'actual'); off = adapter.own_dim + m; col = 0
                        for j in range(m):
                            if j == i:
                                continue
                            blk = x[off + col * adapter.blk_dim: off + (col + 1) * adapter.blk_dim]; col += 1
                            if j not in heard:
                                if np.any(blk[:-8] != 0):
                                    raise AssertionError(f'receiver {i} reads an undelivered payload of {j}')
                                missing_checked += 1
                adapter.remember(views)
            _, _, rec = env.step(acts)
        q.append(float(rec['queue']))
    s = env.episode_summary()
    return dict(queue_sum=float(sum(q)), finished=s['finished_vehicles'], censored_tt=s['travel_time_cityflow_censored'],
                changes={k: float(np.mean(v)) for k, v in changes.items()} if probe else None, missing_checked=missing_checked)


def boot(v, B=10000, seed=0):
    rng = np.random.default_rng(seed); v = np.asarray(v, float)
    return [float(x) for x in np.quantile([v[rng.integers(0, len(v), len(v))].mean() for _ in range(B)], [0.025, 0.975])]


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False)
    h0 = {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}
    ck = torch.load(Path(a.ckpt), weights_only=False)
    sc = Scenarios(out); env0, topo0, _, _ = sc.env(a.seeds[0], a.headways[0])
    adapter = CommAdapter(topo0, N_DEC, env0.action_interval)
    if adapter.schema() != ck['schema']:
        raise SystemExit('adapter schema differs from the checkpoint')
    actor = ActorNet(adapter.dim, ck['config']['hidden']); actor.load_state_dict(ck['actor']); actor.eval()
    mask = torch.as_tensor(adapter.valid_mask()); rng = np.random.default_rng(7)
    eps = [(s, h) for s in a.seeds for h in a.headways]; rows = []; t0 = time.perf_counter()
    for s, h in eps:
        r = dict(episode=f'seed{s}_load{h:g}')
        r['actual'] = run(sc, s, h, 'actor', 'actual', actor, adapter, mask, probe=True, rng=rng)
        for v in VARIANTS[1:]:
            r[v] = run(sc, s, h, 'actor', v, actor, adapter, mask, rng=rng)
        r['full'] = run(sc, s, h, 'actor', 'actual', actor, adapter, mask, full=True, rng=rng)
        r['mp2'] = run(sc, s, h, 'mp2', None, None, adapter, mask)
        r['mp2_full'] = run(sc, s, h, 'mp2', None, None, adapter, mask, full=True)
        rows.append(r)
        print(f'[{time.perf_counter() - t0:.0f}s] {r["episode"]}: ' + ' '.join(f'{k} {r[k]["queue_sum"]:.0f}' for k in
              ['actual', 'full', 'none', 'stale', 'shuffle', 'mp2', 'mp2_full']) +
              ' | input change ' + ' '.join(f'{k} {v:.2f}' for k, v in r['actual']['changes'].items()), flush=True)
    rep = dict(ckpt=a.ckpt, ckpt_it=ck['it'], ckpt_select=ck['select'], episodes=len(rows),
               missing_blocks_checked=int(sum(r['actual']['missing_checked'] for r in rows)), self_check='PASS')
    for k in ['full', 'none', 'stale', 'shuffle', 'mp2', 'mp2_full']:
        rel = [100 * (r[k]['queue_sum'] - r['actual']['queue_sum']) / r['actual']['queue_sum'] for r in rows]
        rep[f'{k}_vs_actual_pct'] = dict(mean=float(np.mean(rel)), ci95=boot(rel), worse_episodes=int(sum(x > 0 for x in rel)))
    rep['mean_queue_sum'] = {k: float(np.mean([r[k]['queue_sum'] for r in rows])) for k in ['actual', 'full', 'none', 'stale', 'shuffle', 'mp2', 'mp2_full']}
    rep['input_action_change_rate'] = {v: float(np.mean([r['actual']['changes'][v] for r in rows])) for v in VARIANTS[1:]}
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'rows.json').write_text(json.dumps(rows, indent=1)); (out / 'report.json').write_text(json.dumps(rep, indent=1))
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), source_hashes=h0, seconds=time.perf_counter() - t0), indent=1))
    print(json.dumps(rep, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ckpt', required=True); p.add_argument('--out', required=True)
    p.add_argument('--seeds', type=int, nargs='+', default=list(range(501, 509)))
    p.add_argument('--headways', type=float, nargs='+', default=[8.0, 16.0])
    main(p.parse_args())
