"""ADAPTIVE: how common and how severe is the quota violation, at scale?

Exhaustive enumeration of rational targets on K arms with a common denominator,
run to a long horizon in exact rational arithmetic.  The earlier pass covered
K in 3..5 and denominators to 30 at horizon 40; this one widens every axis.
"""
import json, time, argparse
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path


def compositions(total, parts):
    """Every way of writing `total` as `parts` positive integers, up to order.

    Generated directly as non-decreasing tuples. The obvious implementation
    walks all C(total-1, parts-1) ordered compositions and keeps the sorted
    ones, which for this sweep means enumerating 442 million tuples to keep
    478 thousand -- a factor of 924 thrown away, and the reason the sweep used
    to take hours rather than minutes.
    """
    def gen(remaining, k, least):
        if k == 1:
            if remaining >= least:
                yield (remaining,)
            return
        top = remaining // k
        for first in range(least, top + 1):
            for rest in gen(remaining - first, k - 1, first):
                yield (first,) + rest
    return list(gen(total, parts, 1))


def greedy(parts, d, T):
    """Largest-deficit-first, in integers.

    Every target here has a common denominator, so the deficit
    t*w_i - N_i equals (t*p_i - N_i*d)/d and the rule can be run entirely in
    integers: the arm served is the one maximising t*p_i - N_i*d, and the bound
    of one is exceeded exactly when that maximum exceeds d. Rational arithmetic
    gives identical answers and is about forty times slower, which is the whole
    reason this sweep used to take hours.
    """
    K = len(parts); N = [0] * K; worst = -1; first = None
    for t in range(T + 1):
        best = -1 << 62; bi = 0
        for i in range(K):
            v = t * parts[i] - N[i] * d
            if v > best:
                best = v; bi = i
        if best > worst:
            worst = best
        if best > d and first is None:
            first = t
        if t < T:
            N[bi] += 1
    return F(worst, d), first


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--kmax', type=int, default=7)
    ap.add_argument('--dmax', type=int, default=60)
    ap.add_argument('--horizon', type=int, default=200)
    a = ap.parse_args()
    t0 = time.time(); rows = []; checked = 0; worst = (F(0), None); earliest = None
    for K in range(3, a.kmax + 1):
        for d in range(K, a.dmax + 1):
            for parts in compositions(d, K):
                w = [F(p, d) for p in parts]
                checked += 1
                wd, fv = greedy(parts, d, a.horizon)
                if fv is not None:
                    rows.append(dict(K=K, den=d, w=[str(x) for x in w],
                                     worst=str(wd), worst_float=float(wd),
                                     first_violation=fv))
                    if wd > worst[0]:
                        worst = (wd, (K, d, [str(x) for x in w]))
                    if earliest is None or fv < earliest: earliest = fv
            if checked and checked % 20000 < 200:
                print(f'K={K} d={d} checked={checked} viol={len(rows)} '
                      f'{time.time()-t0:.0f}s', flush=True)
    rows.sort(key=lambda r: -r['worst_float'])
    # aggregates over EVERY violating target, not only the top of the list
    import collections as _c
    hist_worst = _c.Counter(); hist_first = _c.Counter(); per_K = {}
    for r in rows:
        hist_worst[round(r['worst_float'], 2)] += 1
        hist_first[r['first_violation']] += 1
    for K in range(3, a.kmax + 1):
        sub = [r for r in rows if r['K'] == K]
        tot = sum(1 for d in range(K, a.dmax + 1) for _ in compositions(d, K))
        per_K[str(K)] = dict(
            checked=tot, violating=len(sub),
            fraction=(len(sub) / tot if tot else None),
            worst=(max(r['worst_float'] for r in sub) if sub else None),
            worst_exact=(max(sub, key=lambda r: r['worst_float'])['worst'] if sub else None),
            earliest=(min(r['first_violation'] for r in sub) if sub else None),
            median_worst=(sorted(r['worst_float'] for r in sub)[len(sub) // 2] if sub else None),
            above_one=sum(1 for r in sub if r['worst_float'] > 1.0),
            above_1p5=sum(1 for r in sub if r['worst_float'] > 1.5))
    out = dict(script='EXP_adaptive_bigsearch.py',
               design='exhaustive enumeration of rational targets, exact arithmetic',
               arms=list(range(3, a.kmax + 1)), denominators=f'K..{a.dmax}',
               horizon=a.horizon, targets_checked=checked,
               targets_violating_quota=len(rows),
               violation_fraction=(len(rows) / checked if checked else None),
               worst_deficit=str(worst[0]), worst_at=worst[1],
               earliest_violation=earliest,
               wall_seconds=round(time.time() - t0, 1), top=rows[:40],
               per_K=per_K,
               hist_worst={str(k): v for k, v in sorted(hist_worst.items())},
               hist_first={str(k): v for k, v in sorted(hist_first.items())},
               by_K={str(K): sum(1 for r in rows if r['K'] == K)
                     for K in range(3, a.kmax + 1)})
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out, checked, len(rows), str(worst[0]), earliest,
          f'{time.time()-t0:.0f}s')


if __name__ == '__main__':
    main()
