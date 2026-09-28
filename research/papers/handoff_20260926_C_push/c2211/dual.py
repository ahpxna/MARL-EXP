#!/usr/bin/env python3
"""Dual certificate of the kappa flow LP (cost |x0-x1| at budgets 1..5), counts (2,2,1,1).
Variables: mu_1..mu_5, lp_{k,t}, lm_{k,t} (k=1..5, t=0..3), psi(v) for box states.
maximise psi(0) - (eta/6) * sum(lp+lm)
s.t. psi(v) - psi(v+e_t) - mu_k |v0-v1| - sum_t (lp-lm)_{k,t}(v_t/n_t - k/6) <= 0, k = |v|
     psi(full) = 0, sum mu = 1.
"""
import itertools, sys
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog

N = (2, 2, 1, 1)
M = 6
STATES = [u for u in itertools.product(*[range(n + 1) for n in N])]
FULL = N


def solve_dual(eta, extra_obj=None):
    names = []
    idx = {}

    def var(nm):
        idx[nm] = len(names); names.append(nm)
    for k in range(1, 6):
        var(("mu", k))
    for k in range(1, 6):
        for t in range(4):
            var(("lp", k, t)); var(("lm", k, t))
    for v in STATES:
        var(("psi", v))
    nv = len(names)
    Aub, bub, Aeq, beq = [], [], [], []
    for v in STATES:
        k = sum(v)
        if k == M:
            continue
        for t in range(4):
            if v[t] >= N[t]:
                continue
            w = tuple(v[j] + (1 if j == t else 0) for j in range(4))
            r = np.zeros(nv)
            r[idx[("psi", v)]] += 1
            r[idx[("psi", w)]] -= 1
            if k >= 1:
                r[idx[("mu", k)]] -= abs(v[0] - v[1])
                for s in range(4):
                    coef = v[s] / N[s] - k / 6
                    r[idx[("lp", k, s)]] -= coef
                    r[idx[("lm", k, s)]] += coef
            Aub.append(r); bub.append(0.0)
    r = np.zeros(nv); r[idx[("psi", FULL)]] = 1; Aeq.append(r); beq.append(0.0)
    r = np.zeros(nv)
    for k in range(1, 6):
        r[idx[("mu", k)]] = 1
    Aeq.append(r); beq.append(1.0)
    c = np.zeros(nv)
    c[idx[("psi", (0, 0, 0, 0))]] = -1
    for k in range(1, 6):
        for t in range(4):
            c[idx[("lp", k, t)]] = eta / 6
            c[idx[("lm", k, t)]] = eta / 6
    bounds = []
    for nm in names:
        if nm[0] == "psi":
            bounds.append((None, None))
        else:
            bounds.append((0, None))
    res = linprog(c, A_ub=np.array(Aub), b_ub=np.array(bub), A_eq=np.array(Aeq), b_eq=np.array(beq),
                  bounds=bounds, method="highs-ds")
    assert res.status == 0, res.message
    return -res.fun, dict(zip(names, res.x))


if __name__ == "__main__":
    for eta in [0.0, 0.4, 0.79, 0.8, 1.0]:
        val, sol = solve_dual(eta)
        print(eta, val)
    val, sol = solve_dual(0.4)
    for nm, x in sol.items():
        if abs(x) > 1e-12:
            print(nm, Fr(x).limit_denominator(1000), x)
