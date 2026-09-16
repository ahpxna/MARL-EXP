"""D6: how robust is the necessity construction to the product reference?

The sufficiency half of the margin threshold holds under every product reference.
The necessity half is built under the corner reference.  This sweeps the product
reference q_i(true)=t and asks, at each t, whether Top-C still selects A and what
doubled regret the construction attains.

Every definition below is transcribed from the Lean sources, not reconstructed:

  bit b                 = 1 if b else 0
  gate A j x            = 0 if x j else 1 if (exists i in A, x i) or
                          count(others A j) x >= 2 else 0
  coeff A j mu i        = 0 if i in A else (mu-1 if i=j else 1-mu)
  linear c x            = sum_i c i * bit (x i)
  world A j mu x        = linear (coeff A j mu) x + gate A j x
  bump A rho i          = (rho-1) if i in A else 0          [from bump_sum]
  steered A j rho x     = world A j 1 x + linear (bump A rho) x
  jointWeight q c       = prod_i q i (c i)
  productResponse q F i u = sum_c jointWeight q c * F (update c i u)
  productCompressionLoss H Q S = osc (x |-> H x - sum_{j in S} Q j (x j)) / 2
  corner i u            = 1 if u = false else 0

A self-check runs first: at t=0 the implementation must reproduce the proved
theorem steered_span, namely osc(productResponse corner (steered A j rho) i)
= rho for i in A and 0 otherwise.  The sweep is reported only if that passes.
"""
import json, time, argparse, itertools
from fractions import Fraction as F
from pathlib import Path

import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
import EXP_provenance as _P


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


def joint_weight(t, x):
    """q_i(true)=t, q_i(false)=1-t, identical across coordinates."""
    w = F(1)
    for b in x:
        w *= t if b else (1 - t)
    return w


def product_response(t, Fun, i, u, n, xs):
    s = F(0)
    for c in xs:
        w = joint_weight(t, c)
        if w == 0:
            continue
        cc = list(c); cc[i] = u
        s += w * Fun(tuple(cc))
    return s


def osc_response(t, Fun, i, n, xs):
    vals = [product_response(t, Fun, i, u, n, xs) for u in (False, True)]
    return max(vals) - min(vals)


def compression_loss(Fun, Q, S, n, xs):
    vals = [Fun(x) - sum(Q[j][x[j]] for j in S) for x in xs]
    return (max(vals) - min(vals)) / 2


def run(k, rho, t, n, j, A, xs):
    Fun = lambda x: steered(A, j, rho, n, x)
    Q = {i: {u: product_response(t, Fun, i, u, n, xs) for u in (False, True)}
         for i in range(n)}
    spans = {i: abs(Q[i][True] - Q[i][False]) for i in range(n)}
    top = sorted(range(n), key=lambda i: (-spans[i], i))[:len(A)]
    Ac = [i for i in range(n) if i not in A]
    LA = compression_loss(Fun, Q, list(A), n, xs)
    LAc = compression_loss(Fun, Q, Ac[:len(A)], n, xs)
    return dict(spans={str(i): float(v) for i, v in spans.items()},
                topC_is_A=(set(top) == set(A)),
                L_A=float(LA), L_Ac=float(LAc),
                doubled_regret=float(2 * (LA - LAc)))


def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--out', required=True)
    a = ap.parse_args()
    t0 = time.time()

    # ---- self-check against the proved theorem steered_span, at t = 0 -------
    checks = []
    for n, Asz in ((6, 3), (7, 3), (8, 4)):
        j = n - 1
        A = tuple(range(Asz))
        xs = all_x(n)
        for rho in (F(1), F(3, 2), F(2)):
            Fun = lambda x: steered(A, j, rho, n, x)
            ok = True
            for i in range(n):
                got = osc_response(F(0), Fun, i, n, xs)
                want = rho if i in A else F(0)
                if got != want:
                    ok = False
                    checks.append(dict(n=n, rho=str(rho), i=i,
                                       got=str(got), want=str(want)))
            print(f'self-check n={n} rho={rho}: '
                  f'{"PASS" if ok else "FAIL"}  {time.time()-t0:.0f}s', flush=True)
    if checks:
        Path(a.out).write_text(json.dumps(
            dict(self_check='FAILED', mismatches=checks[:20]), indent=1))
        print('SELF-CHECK FAILED; sweep not run'); return

    # ---- reference sweep ---------------------------------------------------
    rows = []
    ts = [F(0)] + [F(i, 32) for i in range(1, 17)]
    for n, Asz in ((6, 3), (8, 4)):
        j = n - 1; A = tuple(range(Asz)); xs = all_x(n)
        for rho in (F(1), F(5, 4), F(3, 2), F(7, 4), F(2)):
            for t in ts:
                r = run(Asz, rho, t, n, j, A, xs)
                r.update(n=n, A_size=Asz, rho=str(rho), t=str(t), t_float=float(t))
                rows.append(r)
            print(f'n={n} rho={rho} done  {time.time()-t0:.0f}s', flush=True)

    pos = [r for r in rows if r['t_float'] > 0]
    flip = [r for r in pos if not r['topC_is_A']]
    corner_rows = [r for r in rows if r['t_float'] == 0]
    out = dict(provenance=_P.stamp(__file__), script='EXP_d6_reference.py',
               design='product reference q_i(true)=t swept on a 17-point exact grid, '
                      'two sizes, five margins; every definition transcribed from the '
                      'Lean sources and validated at t=0 against the proved '
                      'steered_span before the sweep is reported',
               self_check='PASS',
               t_grid=[str(t) for t in ts],
               cells=len(rows), cells_t_positive=len(pos),
               cells_topC_flips=len(flip),
               flip_fraction=(len(flip) / len(pos) if pos else None),
               corner_all_topC_is_A=all(r['topC_is_A'] for r in corner_rows),
               corner_regret_matches_k_2_minus_rho=all(
                   abs(r['doubled_regret'] - r['A_size'] * (2 - float(F(r['rho'])))) < 1e-9
                   for r in corner_rows),
               rows=rows, wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out,
          f"flips at {len(flip)}/{len(pos)} positive-t cells; "
          f"corner regret matches k(2-rho): {out['corner_regret_matches_k_2_minus_rho']}")


if __name__ == '__main__':
    main()
