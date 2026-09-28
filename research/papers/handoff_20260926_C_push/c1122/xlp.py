"""Exact LP (Fractions): min c.x s.t. A_ub x <= b_ub, A_eq x = b_eq, x >= 0. Dense two-phase simplex, Bland."""
from fractions import Fraction as Fr

def simplex(c, A_ub, b_ub, A_eq, b_eq):
    n = len(c)
    rows = []
    rhs = []
    nslack = len(A_ub)
    # build rows with slacks
    for i, (a, b) in enumerate(zip(A_ub, b_ub)):
        row = [Fr(x) for x in a] + [Fr(0)] * nslack
        row[n + i] = Fr(1)
        rows.append(row); rhs.append(Fr(b))
    for a, b in zip(A_eq, b_eq):
        rows.append([Fr(x) for x in a] + [Fr(0)] * nslack); rhs.append(Fr(b))
    M = len(rows)
    N = n + nslack
    # make rhs >= 0
    for i in range(M):
        if rhs[i] < 0:
            rows[i] = [-x for x in rows[i]]; rhs[i] = -rhs[i]
    # artificials for all rows
    T = [rows[i] + [Fr(1) if j == i else Fr(0) for j in range(M)] + [rhs[i]] for i in range(M)]
    basis = [N + i for i in range(M)]
    W = N + M
    def pivot(r, col):
        pv = T[r][col]
        T[r] = [x / pv for x in T[r]]
        for i in range(M):
            if i != r and T[i][col] != 0:
                f = T[i][col]
                Ti = T[i]; Tr = T[r]
                T[i] = [Ti[j] - f * Tr[j] for j in range(W + 1)]
        basis[r] = col
    def run(cost, allowed):
        while True:
            # reduced costs
            cb = [cost[b] for b in basis]
            best = None
            for j in range(W):
                if not allowed(j) or j in basis:
                    continue
                rc = cost[j] - sum(cb[i] * T[i][j] for i in range(M))
                if rc < 0:
                    best = j
                    break
            if best is None:
                return True
            col = best
            ratio = None; r = None
            for i in range(M):
                if T[i][col] > 0:
                    q = T[i][W] / T[i][col]
                    if ratio is None or q < ratio or (q == ratio and basis[i] < basis[r]):
                        ratio = q; r = i
            if r is None:
                return False  # unbounded
            pivot(r, col)
    # phase 1
    c1 = [Fr(0)] * N + [Fr(1)] * M
    run(c1, lambda j: True)
    if sum(T[i][W] for i in range(M) if basis[i] >= N) != 0:
        return None
    # drive artificials out
    for i in range(M):
        if basis[i] >= N:
            for j in range(N):
                if T[i][j] != 0:
                    pivot(i, j); break
    c2 = [Fr(x) for x in c] + [Fr(0)] * nslack + [Fr(0)] * M
    ok = run(c2, lambda j: j < N)
    assert ok
    x = [Fr(0)] * N
    for i in range(M):
        if basis[i] < N:
            x[basis[i]] = T[i][W]
    val = sum(c2[j] * x[j] for j in range(N))
    # duals: y = c_B B^{-1}; B^{-1} columns are the artificial columns
    cb = [c2[b] for b in basis]
    y = [sum(cb[i] * T[i][N + k] for i in range(M)) for k in range(M)]
    return val, x[:n], y
