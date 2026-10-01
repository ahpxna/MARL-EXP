#!/usr/bin/env python3
"""Is the E3 oracle headroom achievable ex ante, or a HINDSIGHT effect of the realised future arrivals?  (diagnostic;
oracle labels only; no learner, no selector)

The continuation label cont_3(S) of a DEV state is ONE rollout: profile S at step t, then the prefix for t+1, t+2,
under the traffic seed's pre-generated Poisson arrivals.  The candidate-family 'oracle' picks the best S AFTER seeing
those arrivals: an E_future[max_S] object.  A causal selector can at best reach max_S E_future[cont(S) | state at t].
This probe keeps the state at t EXACTLY (every vehicle with startTime < 10 t unchanged) and resamples only the future
arrivals (vehicles with startTime >= 10 t, per route, Poisson with the same mean headway: memoryless, so a valid draw of
the future given the past), K times, and re-evaluates a candidate subset of every DEV state under each future.
Subset per state: the prefix, the stored oracle-best feasible candidate (+84 B - 10 B bid), and --cands random feasible
others (seeded).  Self-checks (abort on failure): under the ORIGINAL flow the recomputed cont equals the stored label for
every evaluated candidate; under every variant flow the prefix trajectory up to t is identical (queues at every earlier
step, order, K and scheduler features z at t).
Reported (per state, then averaged): within-state correlation of candidate gains between futures (reliability);
the hindsight oracle E_f[max_c g] vs the ex-ante oracle max_c E_f[g] on the evaluated subset; the stored oracle-best
candidate's gain on the OTHER futures (does the hindsight pick transfer?).  Evidence class: oracle diagnostic.
"""
from __future__ import annotations
import argparse, gzip, hashlib, json, sys, time
from collections import defaultdict
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_screening import no_oracle_access
from models.marl_hetero_selector import prefix_sets
from scripts.MARL_hetero_target_diag import grant, new_env, scenario
from scripts.MARL_hetero_pilot_collect import H
from scripts.MARL_e3_continuation_labels import Policy, step_with, replay
from scripts.MARL_e3_selector_train import load

SOURCES = ['scripts/MARL_e3_hindsight_probe.py', 'scripts/MARL_e3_continuation_labels.py', 'scripts/MARL_hetero_target_diag.py',
           'envs/external/cityflow_budgeted.py', 'envs/external/cityflow_hetero.py']


class OneScenario:
    """Scenarios-compatible factory for ONE scenario dict (original or variant)."""
    def __init__(self, scen):
        self.scen = scen

    def env(self, seed, load):
        return new_env(self.scen, seed, load)


def variant_scenario(orig, out_dir, t_cut, load, rng):
    """Copy of the original scenario with every vehicle of startTime >= t_cut resampled per route (same mean headway)."""
    src = Path(orig['dir']); out_dir.mkdir(parents=True, exist_ok=False)
    flows = json.loads((src / 'flow.json').read_text()); by = defaultdict(list)
    for f in flows:
        by[tuple(f['route'])].append(f)
    new = [f for f in flows if f['startTime'] < t_cut]; horizon = orig['horizon_s']
    for route, fs in by.items():
        tpl = fs[0]; t = float(t_cut) + float(rng.exponential(load))
        while t < horizon:
            ts = int(t); new.append({'vehicle': dict(tpl['vehicle']), 'route': list(route), 'interval': 1.0, 'startTime': ts, 'endTime': ts})
            t += float(rng.exponential(load))
    cfg = json.loads((src / 'config.json').read_text()); cfg['dir'] = str(out_dir) + '/'
    (out_dir / 'roadnet.json').write_text((src / 'roadnet.json').read_text()); (out_dir / 'flow.json').write_text(json.dumps(new))
    (out_dir / 'config.json').write_text(json.dumps(cfg))
    files = {n: {'path': str(out_dir / n), 'sha256': hashlib.sha256((out_dir / n).read_bytes()).hexdigest()} for n in ('roadnet.json', 'flow.json', 'config.json')}
    return dict(orig, dir=str(out_dir), files=files, n_vehicles=len(new))


def base_until(sc, seed, load, pol, t):
    env, _, _, _ = sc.env(seed, load); q = []
    for _ in range(t):
        with no_oracle_access(env):
            order, K = grant(env)
        q.append(step_with(env, pol, prefix_sets(order, K))[0])
    with no_oracle_access(env):
        z = env.scheduler_context().features(); order, K = grant(env)
    return q, list(order), list(K), [float(x) for x in z]


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
        for st in sorted(by_ep[(seed, load_)], key=lambda s: s['t']):
            t = st['t']; c0 = st['cands'][0]
            ok = [i for i, c in enumerate(st['cands']) if i == 0 or c['bytes'] <= st['b0'] + 74]
            best = max(ok, key=lambda i: st['cands'][i]['cont'])
            rng = np.random.default_rng([seed, int(load_), t, 7])
            others = [i for i in ok if i not in (0, best)]; pick = [0, best] + sorted(rng.choice(others, size=min(a.cands, len(others)), replace=False).tolist())
            q_ref, o_ref, k_ref, z_ref = base_until(so, seed, load_, pol, t)
            if o_ref != st['order'] or k_ref != st['K'] or max(abs(x - y) for x, y in zip(z_ref, st['z'])) > 1e-6:
                raise SystemExit(f'SELF-CHECK FAIL: original replay does not reproduce the stored state {seed}/{load_}/t{t}')
            conts = {0: []}
            for i in pick:
                _, _, q, _ = replay(so, seed, load_, pol, t, [set(s) for s in st['cands'][i]['sets']]); v = -float(sum(q))
                if abs(v - st['cands'][i]['cont']) > 1e-9:
                    raise SystemExit(f'SELF-CHECK FAIL: {seed}/{load_}/t{t}/c{i}: recomputed cont {v} != stored {st["cands"][i]["cont"]}')
                conts[0].append(v)
            for k in range(1, a.futures + 1):
                var = variant_scenario(orig, out / 'var' / f'seed{seed}_load{load_:g}_t{t}_f{k}', 10 * t, load_, np.random.default_rng([seed, int(load_), t, k, 99]))
                sv = OneScenario(var); q_v, o_v, k_v, z_v = base_until(sv, seed, load_, pol, t)
                if q_v != q_ref or o_v != o_ref or k_v != k_ref or max(abs(x - y) for x, y in zip(z_v, z_ref)) > 1e-9:
                    raise SystemExit(f'SELF-CHECK FAIL: variant future {k} changes the state at {seed}/{load_}/t{t}')
                conts[k] = [-float(sum(replay(sv, seed, load_, pol, t, [set(s) for s in st['cands'][i]['sets']])[2])) for i in pick]
            G = np.array([[c - cs[0] for c in cs] for f, cs in sorted(conts.items())])      # futures x candidates, gain vs prefix in the SAME future
            rows.append(dict(episode=f'seed{seed}_load{load_:g}', t=t, picked=pick, stored_best=best, gains=G.tolist()))
            print(f'[{time.perf_counter() - t0:.0f}s] seed{seed}_load{load_:g} t{t}: stored-best gain per future {np.round(G[:, 1], 1).tolist()} | '
                  f'max per future {np.round(G.max(1), 1).tolist()} | ex-ante best {G.mean(0).max():.1f}', flush=True)
            (out / 'rows.json').write_text(json.dumps(rows))
    if h0 != {s: hashlib.sha256((ROOT / s).read_bytes()).hexdigest() for s in SOURCES}:
        raise RuntimeError('source changed during run')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', args=vars(a), states=len(rows), source_hashes=h0,
                                                       seconds=time.perf_counter() - t0), indent=1, default=str))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--actor-dir', required=True); p.add_argument('--futures', type=int, default=3); p.add_argument('--cands', type=int, default=15)
    p.add_argument('--shard', type=int, default=0); p.add_argument('--nshards', type=int, default=1); p.add_argument('--out', required=True)
    main(p.parse_args())
