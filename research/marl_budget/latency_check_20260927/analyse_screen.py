"""Independent re-analysis of a cheap-screen table file (read-only).

For every snapshot and interior budget k, from the raw 2^m value table:
  spread_k        = best k-set value - worst k-set value (how much the choice of S matters)
  regret(method)  = best k-set value - value chosen by method
methods: cached-queue prefix (deployable heuristic), its oracle R1/R2 repair,
true-singleton-gain prefix (oracle score), its oracle R1 repair,
best nested chain (oracle; min over chains of the SUM of regrets over k, and of the MAX).
Aggregation: mean over (snapshot, k) inside each episode, then mean over episodes.
"""
import gzip, json, sys, itertools
from collections import defaultdict

def popc(x): return bin(x).count('1')

def mask(items): return sum(1 << i for i in items)

def reach_best(f, m, P, R):
    ins = [i for i in range(m) if (P >> i) & 1]
    outs = [i for i in range(m) if not (P >> i) & 1]
    v = f[P]
    for r in range(1, R + 1):
        for a in itertools.combinations(ins, r):
            for b in itertools.combinations(outs, r):
                S = P
                for x in a: S &= ~(1 << x)
                for y in b: S |= 1 << y
                v = max(v, f[S])
    return v

def best_chain(f, m, best, agg):
    # DP over chains emptyset -> full; state = current set C at layer k.
    dp = {0: 0.0}
    for k in range(1, m):
        nd = {}
        for C0, v0 in dp.items():
            for i in range(m):
                if not (C0 >> i) & 1:
                    C = C0 | (1 << i)
                    r = best[k] - f[C]
                    val = v0 + r if agg == 'sum' else max(v0, r)
                    if val < nd.get(C, float('inf')):
                        nd[C] = val
        dp = nd
    return min(dp.values())

def main(path):
    rows = [json.loads(l) for l in gzip.open(path, 'rt')]
    per_ep = defaultdict(lambda: defaultdict(list))
    nz = defaultdict(int); tot = 0
    for r in rows:
        f = r['values']; m = r['m']
        layers = {k: [x for x in range(1 << m) if popc(x) == k] for k in range(1, m)}
        best = {k: max(f[x] for x in layers[k]) for k in layers}
        worst = {k: min(f[x] for x in layers[k]) for k in layers}
        gain = [f[1 << i] - f[0] for i in range(m)]
        order = sorted(range(m), key=lambda i: (-gain[i], i))
        heur = r['cached_queue_ranking']
        ep = per_ep[r['episode_id']]
        chain_sum = best_chain(f, m, best, 'sum'); chain_max = best_chain(f, m, best, 'max')
        ep['chain_sum_per_k'].append(chain_sum / (m - 1)); ep['chain_max'].append(chain_max)
        for k in range(1, m):
            tot += 1
            sp = best[k] - worst[k]
            Ph = mask(heur[:k]); Pg = mask(order[:k])
            vals = {
                'heur_prefix': best[k] - f[Ph],
                'heur_R1': best[k] - reach_best(f, m, Ph, 1),
                'heur_R2': best[k] - reach_best(f, m, Ph, 2),
                'gain_prefix': best[k] - f[Pg],
                'gain_R1': best[k] - reach_best(f, m, Pg, 1),
            }
            ep['spread'].append(sp); ep['absbest'].append(abs(best[k]))
            for key, v in vals.items():
                ep[key].append(v)
                ep[key + '_frac'].append(v / sp if sp > 1e-9 else 0.0)
                if v > 1e-9: nz[key] += 1
    keys = ['spread', 'absbest', 'heur_prefix', 'heur_R1', 'heur_R2', 'gain_prefix', 'gain_R1',
            'chain_sum_per_k', 'chain_max', 'heur_prefix_frac', 'heur_R1_frac', 'heur_R2_frac',
            'gain_prefix_frac', 'gain_R1_frac']
    out = {}
    for key in keys:
        eps = [sum(v[key]) / len(v[key]) for v in per_ep.values()]
        out[key] = dict(mean_over_episodes=sum(eps) / len(eps), min_ep=min(eps), max_ep=max(eps))
    out['nonzero_fraction_of_snapshot_budget_pairs'] = {k: nz[k] / tot for k in nz}
    out['n_snapshots'] = len(rows); out['n_episodes'] = len(per_ep); out['pairs'] = tot
    print(json.dumps(out, indent=1))

if __name__ == '__main__':
    main(sys.argv[1])
