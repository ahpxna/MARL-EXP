#!/usr/bin/env python3
"""Typed flow LP for counts (2,2,1,1): g = (a,a,-a,-a,b,-b). Discovery only (floating point)."""
import itertools, sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

N = (2, 2, 1, 1)
M = 6
STATES = [u for u in itertools.product(*[range(n + 1) for n in N])]


def layers():
    return [[u for u in STATES if sum(u) == k] for k in range(M + 1)]


def baseline(w, k):
    return min(abs(sum(wt * ut for wt, ut in zip(w, u))) for u in STATES if sum(u) == k)


def cost_fn(a, b, kappa=False):
    w = (a, -a, b, -b)
    D = 4 * a + 2 * b
    bk = [baseline(w, k) for k in range(M + 1)]
    if kappa:
        return lambda k, v: abs(v[0] - v[1]) * (a - b) / D
    return lambda k, v: (abs(sum(wt * vt for wt, vt in zip(w, v))) - bk[k]) / D


def solve(cost, eta, band=True, want_flow=False):
    L = layers()
    xi, fi = {}, {}
    idx = 0
    for k in range(M + 1):
        for v in L[k]:
            xi[(k, v)] = idx; idx += 1
    for k in range(M):
        for v in L[k]:
            for t in range(4):
                if v[t] < N[t]:
                    fi[(k, v, t)] = idx; idx += 1
    ti = idx; nvar = idx + 1
    Aeq, beq, Aub, bub = [], [], [], []
    Aeq.append({xi[(0, L[0][0])]: 1.0}); beq.append(1.0)
    for k in range(M):
        for v in L[k]:
            r = {xi[(k, v)]: -1.0}
            for t in range(4):
                if (k, v, t) in fi:
                    r[fi[(k, v, t)]] = 1.0
            Aeq.append(r); beq.append(0.0)
        for v2 in L[k + 1]:
            r = {xi[(k + 1, v2)]: -1.0}
            for t in range(4):
                if v2[t] >= 1:
                    v = tuple(v2[j] - (1 if j == t else 0) for j in range(4))
                    if (k, v, t) in fi:
                        r[fi[(k, v, t)]] = 1.0
            Aeq.append(r); beq.append(0.0)
    for k in range(1, M):
        r = {ti: -1.0}
        for v in L[k]:
            c = cost(k, v)
            if c != 0:
                r[xi[(k, v)]] = c
        Aub.append(r); bub.append(0.0)
    if band:
        for k in range(M + 1):
            for t in range(4):
                r = {xi[(k, v)]: v[t] / N[t] for v in L[k] if v[t] != 0}
                Aub.append(dict(r)); bub.append(k / M + eta / M)
                Aub.append({kk: -vv for kk, vv in r.items()}); bub.append(-(k / M - eta / M))

    def mat(rows):
        A = lil_matrix((len(rows), nvar))
        for i, r in enumerate(rows):
            for j, val in r.items():
                A[i, j] = val
        return A.tocsr()
    c = np.zeros(nvar); c[ti] = 1.0
    res = linprog(c, A_ub=mat(Aub), b_ub=np.array(bub), A_eq=mat(Aeq), b_eq=np.array(beq),
                  bounds=[(0, None)] * nvar, method="highs")
    assert res.status == 0, res.message
    if want_flow:
        return res.fun, res.x, xi, fi
    return res.fun


if __name__ == "__main__":
    etas = [i / 40 for i in range(0, 61)]
    for ab in [1.001, 1.01, 1.1, 1.25, 1.5, 2, 2.5, 3, 4, 7, 20, 1000]:
        a, b = ab, 1.0
        cst = cost_fn(a, b)
        cc = (a - b) / (4 * a + 2 * b)
        worst = 0.0
        for e in etas:
            v = solve(cst, e)
            pred = cc * max((2 - e) / 3, 2 / 5)
            worst = max(worst, abs(v - pred) / cc)
        print(f"ratio {ab}: worst relative gap vs conjecture {worst:.2e}", flush=True)
    # kappa problem
    cst = cost_fn(1.0, 0.5, kappa=True)
    cc = 0.5 / 5.0
    worst = 0.0
    for e in etas:
        v = solve(cst, e)
        worst = max(worst, abs(v - cc * max((2 - e) / 3, 2 / 5)) / cc)
    print(f"kappa problem worst relative gap {worst:.2e}")
