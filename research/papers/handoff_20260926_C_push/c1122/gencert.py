"""Generate + verify coordinate certificates (cert6 format) for the 1122 family."""
import itertools, sys
from fractions import Fraction as Fr
from poly import *
n = (1, 1, 2, 2)
box = [v for v in itertools.product(*[range(t + 1) for t in n])]

def cost_poly(v, reg):
    """raw cost as poly in t (b=1) on regime"""
    p, q = v[0] - v[1], v[2] - v[3]
    k = sum(v)
    samp = {'L': Fr(3, 2), 'M': Fr(5, 2), 'H': Fr(4)}[reg]
    s = p * samp + q
    sg = 1 if s > 0 else (-1 if s < 0 else 0)
    ca, cb = sg * p, sg * q
    bl = {1: (0, 1), 5: (0, 1), 3: {'L': (-1, 2), 'M': (1, -2), 'H': (0, 1)}[reg]}.get(k, (0, 0))
    return trim([cb - bl[1], ca - bl[0]])

def succs(v):
    for t in range(4):
        if v[t] < n[t]:
            yield tuple(v[j] + (1 if j == t else 0) for j in range(4))

def dp_at(t, M, Lb, reg):
    psi = {}
    for v in sorted(box, key=lambda v: -sum(v)):
        k = sum(v)
        if k == 6:
            psi[v] = Fr(0); continue
        nc = ev(M.get(k, [0]), t) * ev(cost_poly(v, reg), t) + ev(Lb.get(k, [0]), t) * (v[0] + v[1] - Fr(k, 3))
        psi[v] = nc + min(psi[u] for u in succs(v))
    return psi

def make(name, M, Lb, reg, t0, t1, deg, psi0_expect, inf=False):
    """M, Lb: dict k -> poly in t. deg: degree of potentials in t. t1=None -> [t0, inf)"""
    if inf:
        ts = [t0 + i for i in range(deg + 1)]
    else:
        ts = [t0 + (t1 - t0) * Fr(i, deg) for i in range(deg + 1)]
    tabs = [dp_at(t, M, Lb, reg) for t in ts]
    Psi = {v: interp(ts, [tb[v] for tb in tabs]) for v in box}
    ok = True
    # edge checks
    for v in box:
        k = sum(v)
        if k == 6:
            continue
        nc = add(mul(M.get(k, [0]), cost_poly(v, reg)), sc(v[0] + v[1] - Fr(k, 3), Lb.get(k, [0])))
        for u in succs(v):
            sl = sub(add(nc, Psi[u]), Psi[v])
            if inf:
                assert len(sl) <= 2
                good = ev(sl, t0) >= 0 and (len(sl) < 2 or sl[1] >= 0)
            elif len(sl) <= 2:
                good = ev(sl, t0) >= 0 and ev(sl, t1) >= 0
            else:
                good, cs = bernstein_ok(sl, t0, t1)
            if not good:
                ok = False
                print("EDGE FAIL", name, v, u, sl)
    # sample check vs DP (potential must be <= DP); and psi0
    if Psi[(0, 0, 0, 0)] != trim(psi0_expect):
        ok = False
        print("PSI0 mismatch", name, Psi[(0, 0, 0, 0)], psi0_expect)
    if Psi[(1, 1, 2, 2)] != [0]:
        ok = False
    print(name, "ok" if ok else "FAILED")
    return Psi, ok

def lean_cert(name, M, Lb, Psi, degM, degPsi):
    out = []
    out.append(f"/-- Budget weights of `{name}`. -/")
    out.append(f"noncomputable def M_{name} (a b : ℝ) : ℕ → ℝ")
    for k in range(1, 6):
        if k in M and trim(M[k]) != [0]:
            out.append(f"  | {k} => {fmt_hom(M[k], degM)}")
    out.append("  | _ => 0")
    out.append(f"\n/-- Band multipliers of `{name}`. -/")
    out.append(f"noncomputable def L_{name} (a b : ℝ) : ℕ → ℝ")
    for k in range(1, 6):
        if k in Lb and trim(Lb[k]) != [0]:
            out.append(f"  | {k} => {fmt_hom(Lb[k], degPsi)}")
    out.append("  | _ => 0")
    out.append(f"\n/-- Potentials of `{name}`. -/")
    out.append(f"noncomputable def P_{name} (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ")
    for v in box:
        out.append(f"  | {v[0]}, {v[1]}, {v[2]}, {v[3]} => {fmt_hom(Psi[v], degPsi)}")
    out.append("  | _, _, _, _ => 0\n")
    return "\n".join(out)

certs = []
F = Fr
t = [F(0), F(1)]  # poly 't'
# A (L regime): q=4, M2=M4=1, M3=2, Lb2 = a-b, Lb4 = -(a-b)
MA = {2: [1], 3: [2], 4: [1]}
LA = {2: [-1, 1], 4: [1, -1]}
certs.append(('AL', MA, LA, 'L', F(1), F(2), 1, sc(F(8, 3), [-1, 1]), False, 0, 1))
certs.append(('AM', MA, LA, 'M', F(2), F(5, 2), 1, sc(F(4, 3), [4, -1]), False, 0, 1))
MB = {1: [1], 5: [1]}
LB = {1: [1, -1], 5: [-1, 1]}
certs.append(('Band', MB, LB, 'L', F(1), None, 1, sc(F(2, 3), [-1, 1]), True, 0, 1))
MLf = {2: [1], 3: [2], 4: [1]}
certs.append(('Lf', MLf, {}, 'L', F(1), F(2), 1, [-2, 2], False, 0, 1))
MM1 = {2: [3, -1], 3: [-2, 2], 4: [3, -1]}
certs.append(('M1f', MM1, {}, 'M', F(2), F(7, 3), 2, mul([-2, 2], [3, -1]), False, 1, 2))
MM23 = {1: [3, -1], 2: [3, -1], 3: [-1, 1], 4: [3, -1], 5: [3, -1]}
certs.append(('M23f', MM23, {}, 'M', F(7, 3), F(13, 5), 2, mul([-2, 2], [3, -1]), False, 1, 2))
MU = {k: [1] for k in range(1, 6)}
certs.append(('M4f', MU, {}, 'M', F(13, 5), F(3), 1, [2], False, 0, 1))
certs.append(('Hf', MU, {}, 'H', F(3), None, 1, [-1, 1], True, 0, 1))
allok = True
lean = []
for (name, M, Lb, reg, t0, t1, deg, psi0, inf, degM, degPsi) in certs:
    Psi, ok = make(name, M, Lb, reg, t0, t1, deg, psi0, inf)
    allok &= ok
    lean.append(lean_cert(name, M, Lb, Psi, degM, degPsi))
open("certs_price.lean", "w").write("\n".join(lean))
print("ALL OK" if allok else "SOME FAILED")
