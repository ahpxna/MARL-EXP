"""ADAPTIVE: is the worst deficit of largest-deficit tracking bounded?

The exhaustive census answers how OFTEN the rule exceeds a deficit of one.  It
does not answer how FAR, because its worst case sits against both of its own
search limits: every one of the forty worst targets it found has the maximum
arm count and a denominator within a few of the maximum.  A number pinned to
the edge of a box is a property of the box.

That question is worth separating because the literature already bounds the
same quantity.  Garivier and Kaufmann's Lemma 15 proves that this exact rule --
serve the arm maximising the entitlement shortfall -- keeps every arm within
$K-1$ of its entitlement.  The census exhibits $7/4$.  So the true constant for
the rule lies in $[7/4, K-1]$, and what matters is whether it grows with $K$
like the upper bound does or settles like the exhibited value suggests.

Exhaustive enumeration cannot reach far enough to tell: partitions of $d$ into
$K$ parts grow fast enough that $K\\le10$, $d\\le128$ is already six hundred
million targets.  But the extremal targets are not generic.  Every one of them
is a few tiny arms, one or two middling arms, and one arm carrying most of the
weight -- a partition with a handful of DISTINCT values, not a handful of
parts.  So this enumerates exactly those: all partitions of $d$ into $K$ parts
taking at most a few distinct values, which is a small set even at $K=24$ and
$d=512$.

What that buys is a lower bound, and a lower bound is the side that matters
here: any target it finds is a real target, so a deficit it exhibits is really
attained.  It cannot certify that nothing worse exists outside the restricted
shape, and this does not claim to.

Self-check: on the range the exhaustive census covered, the restricted shape
must recover the same worst deficit the exhaustive search found.  If the
extremal targets were not of this shape the check fails and nothing is
reported.
"""
import argparse
import json
import os
import sys
import time
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import EXP_provenance as _P

# worst deficits the exhaustive sweep (K<=8, d<=64, horizon 240) reported
EXHAUSTIVE_WORST = {3: F(86, 63), 4: F(31, 20), 5: F(33, 20),
                    6: F(95, 56), 7: F(110, 63), 8: F(7, 4)}


def shapes(d, K, maxdistinct):
    """Partitions of d into K positive parts using at most `maxdistinct` values.

    Enumerated by choosing the distinct values and their multiplicities rather
    than by filtering all partitions, so the cost follows the restricted shape
    and not the partition count.
    """
    out = []

    def rec(rem_d, rem_k, least, slots, acc):
        if rem_k == 0:
            if rem_d == 0:
                out.append(tuple(acc))
            return
        if slots == 0 or rem_d < rem_k * least:
            return
        # value v used with multiplicity c
        for v in range(least, rem_d // rem_k + 1):
            for c in range(1, rem_k + 1):
                if v * c > rem_d:
                    break
                rec(rem_d - v * c, rem_k - c, v + 1, slots - 1, acc + [v] * c)
    rec(d, K, 1, maxdistinct, [])
    return out


def greedy_worst(parts, d, T):
    """Largest-deficit-first in integers; returns (worst deficit, first step).

    Every target has a common denominator, so the deficit t*w_i - N_i is
    (t*p_i - N_i*d)/d and the whole run is integer arithmetic: serve the arm
    maximising t*p_i - N_i*d, and the bound of one is exceeded exactly when
    that maximum exceeds d.
    """
    K = len(parts)
    N = [0] * K
    worst_num, first = 0, None
    for t in range(T + 1):
        best_i, best_v = 0, None
        for i in range(K):
            v = t * parts[i] - N[i] * d
            if best_v is None or v > best_v:
                best_i, best_v = i, v
        if best_v > worst_num:
            worst_num = best_v
            if best_v > d and first is None:
                first = t
        if t < T:
            N[best_i] += 1
    return F(worst_num, d), first


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--kmax', type=int, default=24)
    ap.add_argument('--dmax', type=int, default=256)
    ap.add_argument('--horizon', type=int, default=400)
    ap.add_argument('--distinct', type=int, default=4)
    ap.add_argument('--check-kmax', type=int, default=8)
    ap.add_argument('--check-dmax', type=int, default=64)
    a = ap.parse_args()
    t0 = time.time()

    # ---------------- self-check: recover the exhaustive worst -----------
    got = {}
    for K in range(3, a.check_kmax + 1):
        w = F(0)
        for d in range(K, a.check_dmax + 1):
            for p in shapes(d, K, a.distinct):
                wd, _ = greedy_worst(p, d, 240)
                if wd > w:
                    w = wd
        got[K] = w
    bad = {K: (str(got[K]), str(EXHAUSTIVE_WORST[K]))
           for K in got if got[K] != EXHAUSTIVE_WORST.get(K)}
    print(f'self-check: restricted shape reproduces the exhaustive worst on '
          f'{len(got) - len(bad)}/{len(got)} arm counts -> '
          f'{"PASS" if not bad else "FAIL"}  ({time.time()-t0:.0f}s)', flush=True)
    if bad:
        for K, (g, e) in bad.items():
            print(f'   K={K}: restricted {g}, exhaustive {e}')
        raise SystemExit('extremal targets are not of the restricted shape; not reported')

    # ---------------- the frontier ---------------------------------------
    per_K, rows = {}, []
    for K in range(3, a.kmax + 1):
        best, best_t, checked = F(0), None, 0
        for d in range(K, a.dmax + 1):
            for p in shapes(d, K, a.distinct):
                checked += 1
                wd, first = greedy_worst(p, d, a.horizon)
                if wd > best:
                    best, best_t = wd, (d, p, first)
        per_K[K] = dict(worst=str(best), worst_float=float(best),
                        denominator=best_t[0], target=[f'{x}/{best_t[0]}' for x in best_t[1]],
                        first_violation=best_t[2], checked=checked,
                        at_denominator_cap=bool(best_t[0] > a.dmax - 4),
                        gk_bound=K - 1)
        rows.append((K, float(best), best_t[0]))
        print(f'K={K:2d} worst={best} ({float(best):.4f})  d={best_t[0]}  '
              f'checked={checked}  {time.time()-t0:.0f}s', flush=True)

    floats = [r[1] for r in rows]
    rising = all(floats[i] <= floats[i + 1] + 1e-12 for i in range(len(floats) - 1))
    out = dict(provenance=_P.stamp(__file__), script='EXP_adaptive_frontier.py',
               design='partitions of d into K parts with at most a few distinct values, the '
                      'shape every extremal target of the exhaustive census has; a lower '
                      'bound on the worst deficit, pushed past the range exhaustive '
                      'enumeration can reach',
               kmax=a.kmax, dmax=a.dmax, horizon=a.horizon, distinct=a.distinct,
               self_check=dict(arm_counts_checked=sorted(got),
                               reproduced_exhaustive_worst=True,
                               values={str(k): str(v) for k, v in got.items()}),
               monotone_in_K=bool(rising),
               worst_overall=max(floats),
               gk_upper_bound='K-1 (Garivier and Kaufmann, Lemma 15)',
               per_K=per_K, wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print(f'\nwrote {a.out}: worst over all K = {max(floats):.4f}, '
          f'monotone in K = {rising}')


if __name__ == '__main__':
    main()
