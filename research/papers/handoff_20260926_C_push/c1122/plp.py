"""Path-mixture LP for counts (1,1,2,2): p over the 180 type sequences. b = 1, a = r."""
import itertools
import numpy as np
from fractions import Fraction as Fr
from scipy.optimize import linprog

n = (1, 1, 2, 2)
m = 6
seqs = sorted(set(itertools.permutations([0, 1, 2, 2, 3, 3])))
assert len(seqs) == 180

def states(s):
    v = [0, 0, 0, 0]
    out = [tuple(v)]
    for t in s:
        v[t] += 1
        out.append(tuple(v))
    return out

ST = [states(s) for s in seqs]
box = [v for v in itertools.product(*[range(t + 1) for t in n])]

def S(r, v):
    return r * (v[0] - v[1]) + (v[2] - v[3])

def base(r, k):
    return min(abs(S(r, u)) for u in box if sum(u) == k)

def cost(r, v):
    k = sum(v)
    return abs(S(r, v)) - base(r, k)

def solve(r, eta):
    """returns T, p, mu, lup, llo (numerical)"""
    N = len(seqs)
    nv = N + 1
    A, b = [], []
    for k in range(1, 6):
        row = np.zeros(nv)
        for j in range(N):
            row[j] = cost(r, ST[j][k])
        row[N] = -1
        A.append(row); b.append(0.0)
    for k in range(1, 6):
        for t in range(4):
            row = np.zeros(nv)
            for j in range(N):
                row[j] = ST[j][k][t] / n[t]
            A.append(row.copy()); b.append(k / 6 + eta / 6)
            A.append(-row); b.append(-(k / 6 - eta / 6))
    Aeq = np.zeros((1, nv)); Aeq[0, :N] = 1
    c = np.zeros(nv); c[N] = 1
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), A_eq=Aeq, b_eq=[1.0],
                  bounds=[(0, None)] * nv, method="highs-ds")
    assert res.status == 0, res.message
    y = -res.ineqlin.marginals
    mu = y[:5]
    lup = y[5::2]
    llo = y[6::2]
    return res.fun, res.x[:N], mu, lup.reshape(5, 4), llo.reshape(5, 4)
