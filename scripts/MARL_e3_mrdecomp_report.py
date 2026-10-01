#!/usr/bin/env python3
"""Report of the F5b multi-receiver decomposition (MARL_e3_multireceiver_decomp.py shards; read-only).

Per actor and per arm, means over the development states with bootstraps over EPISODES and over TRAFFIC SEEDS of:
  headroom_LS      V_LS - 0             best profile found (family best + multi-receiver local search), over the prefix
  coverage_lb      V_LS - V_famB        what lies outside the scored family (a LOWER bound: local search is not exhaustive)
  bytes_family     V_fam - V_famB       family members excluded by the +84 B cap
  geometry_R1      V_famB - V_famR1     what the radius-1 restriction costs inside the family
  bid_bytes        V_famB - V_famBb     what the 10 B bid's bytes cost (bid arms only)
  estimation       V_own - realised     loss of the arm's choice inside its OWN feasible family (V_famBb or V_famB)
  realised         the arm's realised gain
and, for the local search from the prefix, the number of swaps and receivers used; additivity of the family best.
Refuses to report unless every shard of the actor is COMPLETE (use --allow-partial for a progress view only).
"""
from __future__ import annotations
import argparse, glob, json
from collections import defaultdict
from pathlib import Path
import numpy as np


def boot(v, keys, B=5000, seed=0):
    by = defaultdict(list)
    for x, k in zip(v, keys):
        by[k].append(x)
    K = sorted(by); rng = np.random.default_rng(seed)
    out = [np.mean(np.concatenate([by[K[i]] for i in rng.integers(0, len(K), len(K))])) for _ in range(B)]
    return [round(float(x), 2) for x in np.quantile(out, [0.025, 0.975])]


def stat(v, eps):
    return dict(mean=round(float(np.mean(v)), 2), ci_episode=boot(v, eps), ci_seed=boot(v, [e.split('_')[0] for e in eps]))


def main(a):
    R = Path(a.dir); res = {}
    for actor in a.actors:
        shards = sorted(glob.glob(str(R / f'{actor}_shard[0-9]')))
        done = [Path(s, 'manifest.json').exists() for s in shards]
        if not all(done) and not a.allow_partial:
            raise SystemExit(f'{actor}: {sum(done)}/{len(shards)} shards complete; refusing (use --allow-partial for progress only)')
        rows = [r for s in shards if Path(s, 'rows.json').exists() for r in json.loads(Path(s, 'rows.json').read_text())]
        eps = [r['episode'] for r in rows]; out = dict(states=len(rows), complete=all(done))
        f = lambda k: np.array([r[k] for r in rows], float)
        out['headroom_LS'] = stat(f('V_LS'), eps); out['headroom_family_B'] = stat(f('V_famB'), eps)
        out['coverage_lb'] = stat(f('V_LS') - f('V_famB'), eps); out['bytes_family'] = stat(f('V_fam') - f('V_famB'), eps)
        out['geometry_R1'] = stat(f('V_famB') - f('V_famR1'), eps); out['bid_bytes'] = stat(f('V_famB') - f('V_famBb'), eps)
        out['LS_from_prefix'] = dict(gain=stat(f('V_LSP'), eps), swaps_mean=round(float(f('LSP_swaps').mean()), 2), receivers_mean=round(float(f('LSP_receivers').mean()), 2),
                                     share_of_LS_headroom=round(float(f('V_LSP').sum() / max(f('V_LS').sum(), 1e-9)), 3))
        out['family_best_receivers_mean'] = round(float(f('best_family_receivers').mean()), 2)
        add = [r['additivity'] for r in rows if r['additivity']]
        out['additivity'] = dict(states=len(add), joint_minus_sum_mean=round(float(np.mean([x['joint_gain'] - x['sum_single'] for x in add])), 2) if add else None,
                                 superadditive=int(sum(x['joint_gain'] > x['sum_single'] for x in add)), subadditive=int(sum(x['joint_gain'] < x['sum_single'] for x in add)))
        arms = {}
        for n in rows[0]['arms']:
            real = np.array([r['arms'][n]['realised'] for r in rows]); own = f('V_famBb') if rows[0]['arms'][n]['bid'] else f('V_famB')
            arms[n] = dict(realised=stat(real, eps), estimation=stat(own - real, eps), share_of_family_headroom=round(float(real.sum() / max(own.sum(), 1e-9)), 3))
        out['arms'] = arms; out['rollouts'] = int(f('rollouts').sum()); res[actor] = out
        print(f'== {actor}: {len(rows)} states ({"complete" if out["complete"] else "PARTIAL"}), {out["rollouts"]} rollouts')
        for k in ('headroom_LS', 'headroom_family_B', 'coverage_lb', 'bytes_family', 'geometry_R1', 'bid_bytes'):
            print(f'   {k:18s} {out[k]["mean"]:+7.2f}  ep {out[k]["ci_episode"]}  seed {out[k]["ci_seed"]}')
        print(f'   LS from prefix     {out["LS_from_prefix"]["gain"]["mean"]:+7.2f} with {out["LS_from_prefix"]["swaps_mean"]} swaps on {out["LS_from_prefix"]["receivers_mean"]} receivers '
              f'({100 * out["LS_from_prefix"]["share_of_LS_headroom"]:.0f}% of the LS headroom); family best edits {out["family_best_receivers_mean"]} receivers')
        print(f'   additivity         {out["additivity"]}')
        for n, v in arms.items():
            print(f'   arm {n:12s} realised {v["realised"]["mean"]:+6.2f} {v["realised"]["ci_episode"]} | estimation loss {v["estimation"]["mean"]:+6.2f} '
                  f'{v["estimation"]["ci_episode"]} | {100 * v["share_of_family_headroom"]:.0f}% of its family headroom')
    Path(a.out).write_text(json.dumps(res, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dir', required=True); p.add_argument('--actors', nargs='+', default=['scratch_s3', 'bc_s3'])
    p.add_argument('--out', required=True); p.add_argument('--allow-partial', action='store_true')
    main(p.parse_args())
