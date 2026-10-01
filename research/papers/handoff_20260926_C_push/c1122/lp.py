"""Typed flow LP for counts (1,1,2,2), b=1, a=r. Raw (unnormalised) value T = D*V."""
import itertools
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

n = (1, 1, 2, 2)
m = 6
box = [v for v in itertools.product(*[range(t + 1) for t in n])]
layer = {k: [v for v in box if sum(v) == k] for k in range(m + 1)}
edges = []
for v in box:
    for t in range(4):
        if v[t] < n[t]:
            u = tuple(v[j] + (1 if j == t else 0) for j in range(4))
            edges.append((v, u, t))

def S(r, v):
    return r * (v[0] - v[1]) + (v[2] - v[3])

def base(r, k):
    best = None
    for u in box:
        if sum(u) == k:
            val = abs(S(r, u))
            best = val if best is None or val < best else best
    return best

def solve(r, eta, want_dual=False):
    xi = {v: i for i, v in enumerate(box)}
    fi = {e: len(box) + j for j, e in enumerate(edges)}
    ti = len(box) + len(edges)
    nv = ti + 1
    Aeq, beq = [], []
    Aeq.append({xi[(0, 0, 0, 0)]: 1.0}); beq.append(1.0)
    for v in box:
        if sum(v) < m:
            row = {xi[v]: -1.0}
            for e in edges:
                if e[0] == v:
                    row[fi[e]] = 1.0
            Aeq.append(row); beq.append(0.0)
        if sum(v) > 0:
            row = {xi[v]: -1.0}
            for e in edges:
                if e[1] == v:
                    row[fi[e]] = 1.0
            Aeq.append(row); beq.append(0.0)
    Aub, bub, names = [], [], []
    bk = [base(r, k) for k in range(m + 1)]
    for k in range(1, m):
        row = {ti: -1.0}
        for v in layer[k]:
            c = abs(S(r, v)) - bk[k]
            if c != 0:
                row[xi[v]] = c
        Aub.append(row); bub.append(0.0); names.append(("bud", k))
    for k in range(1, m):
        for t in range(4):
            row = {xi[v]: v[t] / n[t] for v in layer[k] if v[t] != 0}
            Aub.append(dict(row)); bub.append(k / m + eta / m); names.append(("up", k, t))
            Aub.append({a: -b for a, b in row.items()}); bub.append(-(k / m - eta / m)); names.append(("lo", k, t))
    def mat(rows):
        M = lil_matrix((len(rows), nv))
        for i, rr in enumerate(rows):
            for j, val in rr.items():
                M[i, j] = val
        return M.tocsr()
    c = np.zeros(nv); c[ti] = 1.0
    res = linprog(c, A_ub=mat(Aub), b_ub=np.array(bub), A_eq=mat(Aeq), b_eq=np.array(beq),
                  bounds=[(0, None)] * nv, method="highs")
    assert res.status == 0, res.message
    if not want_dual:
        return res.fun
    return res, names, xi, fi, ti
