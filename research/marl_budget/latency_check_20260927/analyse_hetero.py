"""Check 4: one shared broadcast order vs per-receiver sets, heterogeneous receiver budgets.

Reads the v2 tables (read-only).  Per snapshot:
  scale          = mean over k of (best k-set value - worst k-set value) in the homogeneous table
  heur_gap       = best-found shared order value - heuristic shared order value
  per_recv_gain  = per-receiver coordinate-ascent value - best-found shared value (>= 0 by construction)
  comm_effect    = full communication value - no communication value
Both searches are heuristics: per_recv_gain is the improvement FOUND over the best shared
order FOUND, not a certified gap between optima.  Means per episode, then over episodes.
"""
import gzip, json, sys
from collections import defaultdict
import numpy as np

def popc(x): return bin(x).count('1')

def main(path):
    rows = [json.loads(l) for l in gzip.open(path, 'rt')]
    ep = defaultdict(lambda: defaultdict(list))
    for r in rows:
        f = r['values']; m = r['m']; h = r['hetero']
        sp = np.mean([max(f[x] for x in range(1 << m) if popc(x) == k) -
                      min(f[x] for x in range(1 << m) if popc(x) == k) for k in range(1, m)])
        e = ep[r['episode_id']]
        e['scale'].append(sp)
        e['heur_gap'].append(h['v_best_shared'] - h['v_heuristic_shared'])
        e['per_recv_gain'].append(h['v_per_receiver'] - h['v_best_shared'])
        e['per_recv_gain_frac'].append((h['v_per_receiver'] - h['v_best_shared']) / sp if sp > 1e-9 else 0.0)
        e['heur_gap_frac'].append((h['v_best_shared'] - h['v_heuristic_shared']) / sp if sp > 1e-9 else 0.0)
        e['comm_effect'].append(h['v_full_comm'] - h['v_no_comm'])
        e['pr_positive'].append(float(h['v_per_receiver'] > h['v_best_shared'] + 1e-9))
        e['rollouts'].append(h['n_distinct_joint'])
    out = {}
    for key in ['scale', 'heur_gap', 'per_recv_gain', 'heur_gap_frac', 'per_recv_gain_frac',
                'comm_effect', 'pr_positive', 'rollouts']:
        vals = [np.mean(v[key]) for v in ep.values()]
        out[key] = dict(mean_over_episodes=float(np.mean(vals)), min_ep=float(np.min(vals)),
                        max_ep=float(np.max(vals)))
    out['n_snapshots'] = len(rows); out['n_episodes'] = len(ep)
    print(json.dumps(out, indent=1))

if __name__ == '__main__':
    main(sys.argv[1])
