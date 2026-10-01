"""D6: is the reference finding an artefact of the one family that was swept?

The first sweep moved the reference along a single symmetric path,
q_i(true) = t for every coordinate at once, and found the necessity construction
degrading continuously with a breakdown point that grows with the margin. That
leaves the obvious objection unanswered: the path was symmetric, the
construction is symmetric, and a symmetric perturbation may simply be the one
direction in which nothing interesting happens.

This sweep widens it on four axes.

  Dimensions.   n in {6,7,8,9} rather than {6,8}, with |A| in {2,3,4}, so the
                breakdown point can be read as a function of size and of how
                much of the space the selected set occupies.
  Margins.      Nine margins from 1 to 2 rather than five, fine enough to trace
                the breakdown point against the margin rather than sample it.
  Resolution.   A 65-point grid in t, so the breakdown point is located to
                1/64 rather than 1/32.
  Direction.    ASYMMETRIC references: q_i(true) = t_i drawn independently per
                coordinate, plus four structured directions that perturb only
                the selected set, only its complement, only the steered
                coordinate j, or everything except j. If the finding survives
                these it is not an artefact of the symmetric path.

Everything is exact rational arithmetic. The responses of the steered world do
not depend on the reference, so they are tabulated once per (n, A, j, rho) and
reused across every reference -- which is what makes the wider sweep affordable.

Two self-checks must pass before any sweep result is reported, both against
proved statements at t=0, where the theorems apply:
  * steered_span: osc = rho on A and 0 off it;
  * steered_exchange_equality: doubled regret = |A| (2 - rho).
"""
import json
import time
import argparse
import itertools
from fractions import Fraction as F
from pathlib import Path

import numpy as np

MASTER_SEED = 606


def bit(b):
    return F(1) if b else F(0)


def gate(A, j, n, x):
    if x[j]:
        return F(0)
    if any(x[i] for i in A):
        return F(1)
    others = [i for i in range(n) if i != j and i not in A]
    if sum(1 for i in others if x[i]) >= 2:
        return F(1)
    return F(0)


def coeff(A, j, mu, i):
    if i in A:
        return F(0)
    return (mu - 1) if i == j else (1 - mu)


def linear(c, n, x):
    return sum(c(i) * bit(x[i]) for i in range(n))


def world(A, j, mu, n, x):
    return linear(lambda i: coeff(A, j, mu, i), n, x) + gate(A, j, n, x)


def steered(A, j, rho, n, x):
    bump = lambda i: (rho - 1) if i in A else F(0)
    return world(A, j, F(1), n, x) + linear(bump, n, x)


def all_x(n):
    return [tuple(b) for b in itertools.product([False, True], repeat=n)]


def tabulate(A, j, rho, n, xs):
    """The steered world on every configuration; independent of the reference."""
    return {x: steered(A, j, rho, n, x) for x in xs}


def joint_weight(ts, x):
    """Product reference with a possibly different t_i in each coordinate."""
    w = F(1)
    for i, b in enumerate(x):
        w *= ts[i] if b else (1 - ts[i])
    return w


def evaluate(tab, ts, n, xs, A):
    """Top-C verdict and doubled regret under the reference ts."""
    weights = {x: joint_weight(ts, x) for x in xs}
    Q = {}
    for i in range(n):
        vals = []
        for u in (False, True):
            s = F(0)
            for c in xs:
                w = weights[c]
                if w == 0:
                    continue
                cc = list(c); cc[i] = u
                s += w * tab[tuple(cc)]
            vals.append(s)
        Q[i] = {False: vals[0], True: vals[1]}
    spans = {i: abs(Q[i][True] - Q[i][False]) for i in range(n)}
    top = sorted(range(n), key=lambda i: (-spans[i], i))[:len(A)]

    def loss(S):
        vals = [tab[x] - sum(Q[i][x[i]] for i in S) for x in xs]
        return (max(vals) - min(vals)) / 2

    Ac = [i for i in range(n) if i not in A][:len(A)]
    LA, LAc = loss(list(A)), loss(Ac)
    return dict(topC_is_A=(set(top) == set(A)),
                doubled_regret=float(2 * (LA - LAc)),

                span_A_min=float(min(spans[i] for i in A)),
                span_off_max=float(max([spans[i] for i in range(n) if i not in A])))


def j_of(A, n):
    return n - 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--nmax', type=int, default=9)
    ap.add_argument('--tgrid', type=int, default=64)
    ap.add_argument('--random-refs', type=int, default=120)
    a = ap.parse_args()
    t0 = time.time()
    RHOS = [F(1), F(9, 8), F(5, 4), F(11, 8), F(3, 2), F(13, 8), F(7, 4), F(15, 8), F(2)]
    # The exchange equality carries the hypothesis |A^c| = |A|, so the balanced
    # configurations n = 2|A| are the ones the theorems speak about. Unbalanced
    # configurations are swept too, in a separate arm, precisely because the
    # theorem does NOT cover them -- but nothing there is checked against it.
    BAL = [(n, n // 2) for n in range(6, a.nmax + 1, 2) if n // 2 - 1 >= 2]
    UNBAL = [(n, k) for n in range(6, a.nmax + 1) for k in (2, 3, 4, 5)
             if k != n // 2 and 2 <= k <= n - 3]
    SIZES = BAL

    # ---------------- self-checks at t = 0 ------------------------------
    bad = []
    for n, k in SIZES:
        j = n - 1; A = tuple(range(k)); xs = all_x(n)
        for rho in (F(1), F(3, 2), F(2)):
            tab = tabulate(A, j, rho, n, xs)
            zero = [F(0)] * n
            weights = {x: joint_weight(zero, x) for x in xs}
            for i in range(n):
                vals = []
                for u in (False, True):
                    s = F(0)
                    for c in xs:
                        w = weights[c]
                        if w == 0:
                            continue
                        cc = list(c); cc[i] = u
                        s += w * tab[tuple(cc)]
                    vals.append(s)
                got = abs(vals[1] - vals[0])
                want = rho if i in A else F(0)
                if got != want:
                    bad.append(dict(check='steered_span', n=n, k=k, rho=str(rho),
                                    i=i, got=str(got), want=str(want)))
            r = evaluate(tab, zero, n, xs, A)
            want = float(k * (2 - float(rho)))
            if n == 2 * k and abs(r['doubled_regret'] - want) > 1e-9:
                bad.append(dict(check='exchange_equality', n=n, k=k, rho=str(rho),
                                got=r['doubled_regret'], want=want))
        print(f'self-check n={n} |A|={k}: {"PASS" if not bad else "FAIL"}  '
              f'{time.time()-t0:.0f}s', flush=True)
    if bad:
        Path(a.out).write_text(json.dumps(dict(self_check='FAILED',
                                               mismatches=bad[:20]), indent=1))
        print('SELF-CHECK FAILED; sweep not run')
        return

    ts_grid = [F(i, a.tgrid) for i in range(0, a.tgrid // 2 + 1)]
    rows = []
    # ---------------- symmetric path, fine ------------------------------
    for n, k in SIZES:
        j = n - 1; A = tuple(range(k)); xs = all_x(n)
        for rho in RHOS:
            tab = tabulate(A, j, rho, n, xs)
            for t in ts_grid:
                r = evaluate(tab, [t] * n, n, xs, A)
                r.update(family='symmetric', n=n, A_size=k, rho=str(rho),
                         t=str(t), t_float=float(t))
                rows.append(r)
        print(f'symmetric n={n} |A|={k} done  {time.time()-t0:.0f}s', flush=True)

    # ---------------- structured directions -----------------------------
    struct = []
    for n, k in SIZES:
        j = n - 1; A = tuple(range(k)); xs = all_x(n)
        for rho in RHOS:
            tab = tabulate(A, j, rho, n, xs)
            for name, sel in (('only_A', lambda i: i in A),
                              ('only_complement', lambda i: i not in A),
                              ('only_j', lambda i: i == j),
                              ('all_but_j', lambda i: i != j)):
                for t in ts_grid[::2]:
                    ts = [t if sel(i) else F(0) for i in range(n)]
                    r = evaluate(tab, ts, n, xs, A)
                    r.update(family=name, n=n, A_size=k, rho=str(rho),
                             t=str(t), t_float=float(t))
                    struct.append(r)
        print(f'structured n={n} |A|={k} done  {time.time()-t0:.0f}s', flush=True)

    # ---------------- asymmetric random references ----------------------
    rng = np.random.default_rng(MASTER_SEED)
    rand = []
    for n, k in SIZES:
        j = n - 1; A = tuple(range(k)); xs = all_x(n)
        for rho in RHOS:
            tab = tabulate(A, j, rho, n, xs)
            for _ in range(a.random_refs):
                ts = [F(int(rng.integers(0, a.tgrid // 2 + 1)), a.tgrid)
                      for _ in range(n)]
                r = evaluate(tab, ts, n, xs, A)
                r.update(family='random', n=n, A_size=k, rho=str(rho),
                         t=[str(x) for x in ts],
                         t_mean=float(sum(ts) / n), t_max=float(max(ts)))
                rand.append(r)
        print(f'random n={n} |A|={k} done  {time.time()-t0:.0f}s', flush=True)

    # ---------------- unbalanced configurations, outside the theorem -----
    unbal = []
    for n, k in UNBAL:
        j = n - 1; A = tuple(range(k)); xs = all_x(n)
        for rho in RHOS:
            tab = tabulate(A, j, rho, n, xs)
            for t in ts_grid[::2]:
                r = evaluate(tab, [t] * n, n, xs, A)
                r.update(family='unbalanced', n=n, A_size=k, rho=str(rho),
                         t=str(t), t_float=float(t),
                         corner_matches_exchange=None)
                unbal.append(r)
        print(f'unbalanced n={n} |A|={k} done  {time.time()-t0:.0f}s', flush=True)

    def onset(sub):
        s = sorted(sub, key=lambda r: F(r['t']))
        f = [r for r in s if F(r['t']) > 0 and not r['topC_is_A']]
        return f[0]['t'] if f else None

    onsets = {}
    monotone_all = True
    for n, k in SIZES:
        for rho in RHOS:
            sub = [r for r in rows if r['n'] == n and r['A_size'] == k
                   and r['rho'] == str(rho)]
            onsets[f'{n}|{k}|{rho}'] = onset(sub)
            seq = [r['topC_is_A'] for r in sorted(sub, key=lambda r: F(r['t']))]
            if seq != sorted(seq, reverse=True):
                monotone_all = False

    def rate(rs):
        # t_float == 0.0 is falsy, so "(r.get('t_float', 1) or 1) > 0" silently kept
        # the corner rows -- which never flip -- in the denominator and diluted every
        # rate. Test for the key's presence, not its truthiness.
        pos = [r for r in rs
               if r['family'] == 'random' or r.get('t_float', 1.0) > 0.0]
        return (sum(1 for r in pos if not r['topC_is_A']) / len(pos)) if pos else None

    out = dict(script='EXP_d6_reference_wide.py',
               design='exact rational sweep of the product reference on four axes: '
                      f'n up to {a.nmax}, |A| in 2..4, nine margins, a '
                      f'{len(ts_grid)}-point symmetric grid, four structured '
                      f'directions, and {a.random_refs} independent asymmetric '
                      'references per configuration; responses tabulated once per '
                      'configuration because they do not depend on the reference',
               master_seed=MASTER_SEED, sizes=[list(s) for s in SIZES],
               rhos=[str(r) for r in RHOS], t_grid=[str(t) for t in ts_grid],
               self_check='PASS (steered_span and steered_exchange_equality at t=0)',
               onset_monotone_in_t=bool(monotone_all), onsets=onsets,
               symmetric_flip_rate=rate(rows), structured_flip_rate=rate(struct),
               random_flip_rate=rate(rand), unbalanced_flip_rate=rate(unbal),
               balanced_sizes=[list(x) for x in BAL],
               unbalanced_sizes=[list(x) for x in UNBAL],
               rows=rows, structured=struct, random=rand, unbalanced=unbal,
               wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out, 'symmetric', len(rows), 'structured', len(struct),
          'random', len(rand), 'unbalanced', len(unbal), 'monotone', monotone_all,
          'flip rates %.3f / %.3f / %.3f' % (out['symmetric_flip_rate'] or 0,
                                             out['structured_flip_rate'] or 0,
                                             out['random_flip_rate'] or 0))


if __name__ == '__main__':
    main()
