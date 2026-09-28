"""Flow LP for g = (a,a,-a,-a,b,b,-b,-b), counts (2,2,2,2), m = 8, interior budgets 1..7.
Floating point discovery only (HiGHS)."""
import itertools
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

N = (2, 2, 2, 2)
M = 8
D_TYPES = 4
STATES = [u for u in itertools.product(*[range(n + 1) for n in N])]
LAYERS = [[u for u in STATES if sum(u) == k] for k in range(M + 1)]


def ssum(w, v):
    return sum(wt * vt for wt, vt in zip(w, v))


def baseline(w, k):
    return min(abs(ssum(w, u)) for u in LAYERS[k])


class LP:
    def __init__(self):
        xi = {}
        idx = 0
        for k, L in enumerate(LAYERS):
            for v in L:
                xi[(k, v)] = idx
                idx += 1
        fi = {}
        for k in range(M):
            for v in LAYERS[k]:
                for t in range(D_TYPES):
                    if v[t] < N[t]:
                        fi[(k, v, t)] = idx
                        idx += 1
        self.xi, self.fi, self.ti = xi, fi, idx
        self.nvar = idx + 1
        eq = []
        beq = []
        eq.append({xi[(0, LAYERS[0][0])]: 1.0}); beq.append(1.0)
        self.eq_out = {}
        self.eq_in = {}
        for k in range(M):
            for v in LAYERS[k]:
                row = {xi[(k, v)]: -1.0}
                for t in range(D_TYPES):
                    if (k, v, t) in fi:
                        row[fi[(k, v, t)]] = 1.0
                self.eq_out[(k, v)] = len(eq)
                eq.append(row); beq.append(0.0)
            for v2 in LAYERS[k + 1]:
                row = {xi[(k + 1, v2)]: -1.0}
                for t in range(D_TYPES):
                    if v2[t] >= 1:
                        v = tuple(v2[j] - (1 if j == t else 0) for j in range(D_TYPES))
                        if (k, v, t) in fi:
                            row[fi[(k, v, t)]] = 1.0
                self.eq_in[(k + 1, v2)] = len(eq)
                eq.append(row); beq.append(0.0)
        self.eq, self.beq = eq, beq

    def solve(self, w, eta, band=True, budgets=range(1, M)):
        xi, ti = self.xi, self.ti
        D = sum(abs(wt) * nt for wt, nt in zip(w, N))
        b = [baseline(w, k) for k in range(M + 1)]
        ub, bub, tags = [], [], []
        for k in budgets:
            row = {ti: -1.0}
            for v in LAYERS[k]:
                c = (abs(ssum(w, v)) - b[k]) / D
                if c != 0:
                    row[xi[(k, v)]] = c
            ub.append(row); bub.append(0.0); tags.append(("cost", k))
        if band:
            for k in range(1, M):
                for t in range(D_TYPES):
                    row = {xi[(k, v)]: v[t] / N[t] for v in LAYERS[k] if v[t] != 0}
                    ub.append(dict(row)); bub.append(k / M + eta / M); tags.append(("hi", k, t))
                    ub.append({kk: -vv for kk, vv in row.items()}); bub.append(-(k / M - eta / M)); tags.append(("lo", k, t))

        def mat(rows):
            A = lil_matrix((len(rows), self.nvar))
            for i, r in enumerate(rows):
                for j, val in r.items():
                    A[i, j] = val
            return A.tocsr()
        c = np.zeros(self.nvar); c[ti] = 1.0
        res = linprog(c, A_ub=mat(ub), b_ub=np.array(bub), A_eq=mat(self.eq), b_eq=np.array(self.beq),
                      bounds=[(0, None)] * self.nvar, method="highs")
        if res.status != 0:
            raise RuntimeError(res.message)
        res.tags = tags
        res.D = D
        res.b = b
        # slope dV/deta = (1/M) * sum of band marginals (<=0)
        slope = 0.0
        for tg, mu in zip(tags, res.ineqlin.marginals):
            if tg[0] in ("hi", "lo"):
                slope += mu / M
        res.slope = slope
        return res


_lp = None


def value(r, eta, band=True):
    global _lp
    if _lp is None:
        _lp = LP()
    w = [r, -r, 1.0, -1.0]
    res = _lp.solve(w, eta, band)
    return res.fun, res.slope, res


def frontier(r, eta_max=8.0, tol=1e-10):
    """Exact-ish piecewise linear frontier in eta via tangent intersection."""
    lines = {}

    def tang(e):
        v, s, _ = value(r, e)
        return (v - s * e, s)  # intercept, slope
    lo, hi = 0.0, eta_max
    L0 = tang(lo)
    L1 = tang(hi)
    bps = []
    stack = [(lo, L0, hi, L1)]
    pieces = [L0, L1]
    while stack:
        e0, A, e1, B = stack.pop()
        if abs(A[1] - B[1]) < 1e-12:
            continue
        ex = (B[0] - A[0]) / (A[1] - B[1])
        if ex <= e0 + 1e-12 or ex >= e1 - 1e-12:
            continue
        vx = A[0] + A[1] * ex
        v, s, _ = value(r, ex)
        if abs(v - vx) < tol:
            bps.append(ex)
        else:
            C = (v - s * ex, s)
            stack.append((e0, A, ex, C))
            stack.append((ex, C, e1, B))
    bps.sort()
    return bps
