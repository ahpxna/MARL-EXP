"""Feature points of the 180 sequences, costs as linear forms in r (b=1), per cost regime."""
import itertools
from fractions import Fraction as Fr
from plp import seqs, ST, box

# linear form: (coef_r, const)
def S_lin(v):
    return (v[0] - v[1], v[2] - v[3])

def val(l, r):
    return l[0] * r + l[1]

def cost_lin(v, regime):
    """regime 'L': 1<r<=2, 'M': 2<=r<=3, 'H': r>=3. returns linear form of |S|-b_k"""
    k = sum(v)
    s = S_lin(v)
    # sign of S on regime: sample point
    rs = {'L': Fr(3, 2), 'M': Fr(5, 2), 'H': Fr(4)}[regime]
    sg = 1 if val(s, rs) > 0 else (-1 if val(s, rs) < 0 else 0)
    ab = (sg * s[0], sg * s[1])
    b = {0: (0, 0), 1: (0, 1), 2: (0, 0), 4: (0, 0), 5: (0, 1), 6: (0, 0),
         3: {'L': (-1, 2), 'M': (1, -2), 'H': (0, 1)}[regime]}[k]
    return (ab[0] - b[0], ab[1] - b[1])

def features(j, regime):
    st = ST[j]
    s = seqs[j]
    c = [cost_lin(st[k], regime) for k in range(7)]
    u1 = (Fr(c[1][0] + c[5][0], 2), Fr(c[1][1] + c[5][1], 2))
    u2 = (Fr(c[2][0] + c[4][0], 2), Fr(c[2][1] + c[4][1], 2))
    u3 = (Fr(c[3][0]), Fr(c[3][1]))
    A = [1 if t in (0, 1) else 0 for t in s]
    a1 = Fr(A[0] + A[5], 2)
    a2 = Fr(A[0] + A[1] + A[4] + A[5], 2)
    return (u1, u2, u3, a1, a2)

if __name__ == "__main__":
    for regime in "LMH":
        pts = {}
        for j in range(180):
            f = features(j, regime)
            pts.setdefault(f, []).append(''.join('AaBb'[t] for t in seqs[j]))
        print(regime, len(pts))
        for f, l in sorted(pts.items(), key=lambda x: (x[0][3], x[0][4])):
            def fl(x):
                return f"{x[0]}r{'+' if x[1]>=0 else ''}{x[1]}"
            print("  u=", fl(f[0]), fl(f[1]), fl(f[2]), " a1=", f[3], " a2=", f[4], " n=", len(l), l[:3])
