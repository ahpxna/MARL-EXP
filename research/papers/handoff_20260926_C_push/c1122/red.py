"""Reduced (symmetric) LP over feature points. T(r,eta) exact. Points per regime."""
from fractions import Fraction as Fr
from feat import features, seqs
from xlp import simplex

def regime(r):
    return 'L' if r <= 2 else ('M' if r <= 3 else 'H')

def points(r):
    reg = regime(r)
    pts = {}
    for j in range(180):
        f = features(j, reg)
        u = tuple(x[0] * r + x[1] for x in f[:3])
        key = (u, f[3], f[4])
        pts.setdefault(key, j)
    return pts  # key -> representative seq index

def solve(r, eta):
    pts = points(r)
    keys = list(pts.keys())
    N = len(keys)
    # vars: p_0..p_{N-1}, t
    c = [0] * N + [1]
    A, b = [], []
    for k in range(3):
        A.append([keys[i][0][k] for i in range(N)] + [-1]); b.append(0)
    A.append([keys[i][1] for i in range(N)] + [0]); b.append(Fr(1, 3) + eta / 3)
    A.append([-keys[i][1] for i in range(N)] + [0]); b.append(-(Fr(1, 3) - eta / 3))
    A.append([keys[i][2] for i in range(N)] + [0]); b.append(Fr(2, 3) + eta / 3)
    A.append([-keys[i][2] for i in range(N)] + [0]); b.append(-(Fr(2, 3) - eta / 3))
    Aeq = [[1] * N + [0]]; beq = [1]
    val, x, y = simplex(c, A, b, Aeq, beq)
    mu = [-y[0], -y[1], -y[2]]
    lam1 = -y[3] + y[4]  # multiplier on a1 >= .. minus on a1 <= ..
    lam2 = -y[5] + y[6]
    supp = [(x[i], ''.join('AaBb'[t] for t in seqs[pts[keys[i]]]), keys[i]) for i in range(N) if x[i] != 0]
    return val, mu, (y[3], y[4], y[5], y[6]), supp

if __name__ == "__main__":
    import sys
    from plp import solve as nsolve
    for r in [Fr(3, 2), Fr(11, 5), Fr(12, 5), Fr(5, 2), Fr(51, 20), Fr(14, 5), Fr(7, 2)]:
        for eta in [Fr(0), Fr(1, 10), Fr(3, 10), Fr(1, 2), Fr(4, 5), Fr(6, 5)]:
            val, mu, y, supp = solve(r, eta)
            nv = nsolve(float(r), float(eta))[0]
            print(r, eta, val, float(val), f"num={nv:.6f}", "mu=", mu, "y=", y)
