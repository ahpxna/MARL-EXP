from fractions import Fraction as Fr
from pieces import pieces
from red import solve
pts = []
for j in range(0, 13):
    r = Fr(7, 3) + (Fr(13, 5) - Fr(7, 3)) * Fr(j, 12)
    L0, bps = pieces(r)
    lines = [L0] + [lb for _, (la, lb) in bps]
    etas = [e for e, _ in bps]
    if len(lines) < 3:
        continue
    Phi, S = lines[-2]
    e1 = etas[-2]
    val, mu, y, supp = solve(r, (etas[-2] + etas[-1]) / 2)
    pts.append((r - 1, Phi, S, e1, mu, y))
def gauss(A, bvec):
    n = len(A); M = [row[:] + [bb] for row, bb in zip(A, bvec)]
    for c in range(n):
        piv = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c] / M[c][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]
def fit(vals, dn, dd):
    # v*(1+q1 x+..)=p0+..; unknowns p0..p_dn, q1..q_dd
    nun = dn + 1 + dd
    A, B = [], []
    for x, v in vals[:nun]:
        A.append([x ** i for i in range(dn + 1)] + [-v * x ** i for i in range(1, dd + 1)]); B.append(v)
    try:
        sol = gauss(A, B)
    except StopIteration:
        return None
    p, q = sol[:dn + 1], [Fr(1)] + sol[dn + 1:]
    ok = all(sum(pi * x ** i for i, pi in enumerate(p)) == v * sum(qi * x ** i for i, qi in enumerate(q)) for x, v in vals)
    return (p, q) if ok else None
for nm, idx in (("S", 2), ("Phi", 1), ("eta1", 3)):
    vals = [(pt[0], pt[idx]) for pt in pts]
    for dn in range(0, 5):
        for dd in range(0, 4):
            if dn + 1 + dd <= len(vals) - 2:
                f = fit(vals, dn, dd)
                if f:
                    print(nm, dn, dd, "num", [str(c) for c in f[0]], "den", [str(c) for c in f[1]])
                    break
        else:
            continue
        break
for k in range(3):
    vals = [(pt[0], pt[4][k]) for pt in pts]
    for dn in range(0, 4):
        f = None
        for dd in range(0, 4):
            if dn + 1 + dd <= len(vals) - 2:
                f = fit(vals, dn, dd)
                if f:
                    print("mu", k, dn, dd, "num", [str(c) for c in f[0]], "den", [str(c) for c in f[1]]); break
        if f:
            break
print(len(pts), "points")
