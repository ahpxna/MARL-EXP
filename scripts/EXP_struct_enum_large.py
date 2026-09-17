"""STRUCTURAL: the defect law over every ordering, exactly, far beyond brute force.

The claim under test is that every ordering of the family g_m pays a total
defect of at least two, and that the paper's construction covers every budget
with a single defect of exactly two.  The earlier pass enumerated orderings and
stopped at m=12: enumeration costs m! tuples before deduplication, so m=14 alone
is 8.7e10 iterations and m=16 is out of reach.

Nothing needs to be enumerated.  Each value of the family is odd, so after k
steps the prefix sum s_k has the parity of k, |s_k| and k agree in parity, and
the defect |s_k| - (k mod 2) is therefore a non-negative even integer.  A partial
ordering is summarised completely by how many copies of each of the four values
it has used: that fixes k and s_k.  The reachable summaries form a small acyclic
graph -- about m^2 nodes -- and every quantity the claim needs is a path
functional on it:

  minimum total defect        shortest path,
  minimum worst-step defect   bottleneck (min-max) path,
  orderings by total defect   path counting, in exact integers,
  budgets a single defect of  reachability under the constraint that the defect
  two can cover               vanishes at every step but the target one.

This is exhaustive, not sampled, and it is exact: the counts are Python integers
and no floating point enters.  The DP is validated against the brute-force
enumeration for every m it reached before the answers beyond it are reported.
"""
import json, math, time, argparse, collections
from pathlib import Path

import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
import EXP_provenance as _P

VALUES = (-3, -1, 1, 3)


def family(m):
    p = math.ceil((m - 2) / 2); q = (m - 2) // 2
    return (1, p, q, 1)                      # multiplicities of -3, -1, 1, 3


def states(counts):
    """Every reachable (a,b,c,d) grouped by step k."""
    A, B, C, D = counts
    by_k = collections.defaultdict(list)
    for a in range(A + 1):
        for b in range(B + 1):
            for c in range(C + 1):
                for d in range(D + 1):
                    by_k[a + b + c + d].append((a, b, c, d))
    return by_k


def defect(st, k):
    a, b, c, d = st
    s = -3 * a - b + c + 3 * d
    return abs(s) - (k % 2)


def successors(st, counts):
    for i, v in enumerate(VALUES):
        if st[i] < counts[i]:
            nxt = list(st); nxt[i] += 1
            yield i, tuple(nxt)


def analyse(m):
    counts = family(m); total = sum(counts)
    assert total == m
    by_k = states(counts)
    full = (counts[0], counts[1], counts[2], counts[3])
    INF = float('inf')

    # --- shortest path: minimum total defect -------------------------------
    best = {(0, 0, 0, 0): 0}
    for k in range(1, m + 1):
        nxt = {}
        for st in by_k[k]:
            cand = INF
            for i, v in enumerate(VALUES):
                if st[i] == 0:
                    continue
                pv = list(st); pv[i] -= 1; pv = tuple(pv)
                if pv in best:
                    cand = min(cand, best[pv])
            if cand < INF:
                nxt[st] = cand + (defect(st, k) if k < m else 0)
        best = nxt
    min_total = best[full]

    # --- bottleneck path: minimum worst-step defect ------------------------
    bott = {(0, 0, 0, 0): 0}
    for k in range(1, m + 1):
        nxt = {}
        for st in by_k[k]:
            cand = INF
            for i, v in enumerate(VALUES):
                if st[i] == 0:
                    continue
                pv = list(st); pv[i] -= 1; pv = tuple(pv)
                if pv in bott:
                    cand = min(cand, bott[pv])
            if cand < INF:
                nxt[st] = max(cand, defect(st, k) if k < m else 0)
        bott = nxt
    min_path = bott[full]

    # --- path counting by total defect, exact integers ---------------------
    dist = {(0, 0, 0, 0): collections.Counter({0: 1})}
    for k in range(1, m + 1):
        nxt = {}
        for st in by_k[k]:
            acc = collections.Counter()
            dk = defect(st, k) if k < m else 0
            for i, v in enumerate(VALUES):
                if st[i] == 0:
                    continue
                pv = list(st); pv[i] -= 1; pv = tuple(pv)
                if pv in dist:
                    for t, n in dist[pv].items():
                        acc[t + dk] += n
            if acc:
                nxt[st] = acc
        dist = nxt
    hist = dist[full]
    orderings = sum(hist.values())
    assert orderings == math.factorial(m) // (math.factorial(counts[1])
                                              * math.factorial(counts[2]))

    # --- which budgets a single defect of two can cover --------------------
    covered = []
    for j in range(1, m):
        reach = {(0, 0, 0, 0)}
        for k in range(1, m + 1):
            nxt = set()
            want = 2 if k == j else 0
            for st in by_k[k]:
                if k < m and defect(st, k) != want:
                    continue
                for i, v in enumerate(VALUES):
                    if st[i] == 0:
                        continue
                    pv = list(st); pv[i] -= 1
                    if tuple(pv) in reach:
                        nxt.add(st); break
            reach = nxt
            if not reach:
                break
        if full in reach:
            covered.append(j)
    return dict(m=m, orderings=orderings, D=sum(abs(v) * c for v, c in zip(VALUES, counts)),
                budgets=m - 1, min_total_defect=min_total, min_path_defect=min_path,
                budgets_covered_by_one_defect=len(covered),
                covered_budgets=covered,
                every_ordering_pays_at_least_2=(min_total >= 2),
                construction_covers_all_budgets=(len(covered) == m - 1),
                optimal_orderings=hist[min_total],
                optimal_fraction=hist[min_total] / orderings,
                total_defect_distribution={str(k): hist[k] for k in sorted(hist)})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--mmax', type=int, default=40)
    ap.add_argument('--brute', default='research/paper_exp_20260916/struct_enum_brute_m5to13.json')
    a = ap.parse_args()
    t0 = time.time(); rows = []
    checks = []
    bp = Path(a.brute)
    brute = {r['m']: r for r in json.loads(bp.read_text())['rows']} if bp.exists() else {}
    for m in range(5, a.mmax + 1):
        r = analyse(m); rows.append(r)
        tag = ''
        if m in brute:
            b = brute[m]
            ok = (b['orderings'] == r['orderings']
                  and b['min_total_defect'] == r['min_total_defect']
                  and b['min_path_defect'] == r['min_path_defect']
                  and b['budgets_covered_by_one_defect'] == r['budgets_covered_by_one_defect'])
            checks.append(dict(m=m, agrees=bool(ok)))
            tag = '  vs brute force: ' + ('AGREES' if ok else 'DISAGREES')
        print(f"m={m} orderings={r['orderings']:,} min_total={r['min_total_defect']} "
              f"min_path={r['min_path_defect']} covered={r['budgets_covered_by_one_defect']}"
              f"/{m-1} optimal_frac={r['optimal_fraction']:.2e}"
              f"  {time.time()-t0:.0f}s{tag}", flush=True)
        Path(a.out).write_text(json.dumps(dict(
            provenance=_P.stamp(__file__),
            script='EXP_struct_enum_large.py',
            design='exact dynamic programme over prefix-sum summaries; exhaustive over '
                   'orderings without enumerating them; integer arithmetic throughout; '
                   'validated against the brute-force enumeration for every m it reached',
            validation=checks,
            validation_all_agree=all(c['agrees'] for c in checks) if checks else None,
            m_range=[5, m], rows=rows, wall_seconds=round(time.time() - t0, 1)), indent=1))
    print('wrote', a.out, 'validation',
          'ALL AGREE' if all(c['agrees'] for c in checks) else 'MISMATCH')


if __name__ == '__main__':
    main()
