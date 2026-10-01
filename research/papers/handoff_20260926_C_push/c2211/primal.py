#!/usr/bin/env python3
"""Sparse primal laws over type sequences for counts (2,2,1,1). Types: 0=+a,1=-a,2=+b,3=-b."""
import itertools, sys
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

N = (2, 2, 1, 1)
M = 6
SEQS = sorted(set(itertools.permutations([0, 0, 1, 1, 2, 3])))


def counts(s, k):
    return tuple(sum(1 for j in range(k) if s[j] == t) for t in range(4))


def true_cost_coeffs(v, k):
    """cost*1 = alpha*a + beta*b - b_k, returned as (alpha, beta') with baseline included."""
    A = v[0] - v[1]; B = v[2] - v[3]
    bk = 1 if k % 2 == 1 else 0  # baseline coefficient of b
    if A != 0:
        sg = 1 if A > 0 else -1
        return (abs(A), sg * B - bk)
    return (0, abs(B) - bk)


def tight(s):
    for k in range(1, 6):
        v = counts(s, k)
        al, be = true_cost_coeffs(v, k)
        # cost = al*a + be*b ; kappa = |A| = al ; tight iff be == -al
        if be != -al:
            return False
    return True


def kappa(s, k):
    v = counts(s, k)
    return abs(v[0] - v[1])


def solve(eta, bound, only_tight=True, fixed=None):
    S = [s for s in SEQS if (tight(s) or not only_tight)]
    n = len(S)
    # vars: w (n), z (n)
    A, lo, hi = [], [], []

    def row(wc, zc=None):
        r = np.zeros(2 * n)
        r[:n] = wc
        if zc is not None:
            r[n:] = zc
        return r
    A.append(row(np.ones(n))); lo.append(1); hi.append(1)
    for k in range(1, 6):
        A.append(row(np.array([kappa(s, k) for s in S], float))); lo.append(-np.inf); hi.append(bound)
        for t in range(4):
            A.append(row(np.array([counts(s, k)[t] / N[t] for s in S])))
            lo.append(k / 6 - eta / 6); hi.append(k / 6 + eta / 6)
    for j in range(n):
        r = np.zeros(2 * n); r[j] = 1; r[n + j] = -1
        A.append(r); lo.append(-np.inf); hi.append(0)
    c = np.concatenate([np.zeros(n), np.ones(n)])
    integ = np.concatenate([np.zeros(n), np.ones(n)])
    res = milp(c, constraints=LinearConstraint(np.array(A), lo, hi), integrality=integ,
               bounds=Bounds(np.zeros(2 * n), np.ones(2 * n)))
    assert res.status == 0, res.message
    w = res.x[:n]
    sol = [(S[j], w[j]) for j in range(n) if w[j] > 1e-9]
    return sol


def name(s):
    return "".join("AaBb"[t] for t in s)


if __name__ == "__main__":
    print("tight sequences:", sum(1 for s in SEQS if tight(s)), "of", len(SEQS))
    for eta, bound in [(0.0, 2 / 3), (0.8, 0.4)]:
        sol = solve(eta, bound)
        print(f"eta={eta} bound={bound}: support {len(sol)}")
        for s, w in sol:
            print("  ", name(s), Fr(w).limit_denominator(1000), [kappa(s, k) for k in range(1, 6)])
