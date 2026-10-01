"""Global sequence table + flows (W over the table, Q) for the price module; exact checks."""
import itertools
from fractions import Fraction as Fr
from poly import *
from full import orbit, states, T2I
import sys, io
_o = sys.stdout; sys.stdout = io.StringIO()
from gencert import cost_poly
sys.stdout = _o
n = (1, 1, 2, 2)
ORB = ['AbaBBb', 'BaBbAb', 'BaAbBb', 'AaBbBb', 'BBaAbb', 'BbAaBb']
SEQ = []
OIDX = []
for oi, rep in enumerate(ORB):
    for s in orbit(rep):
        SEQ.append(s); OIDX.append(oi)
N = len(SEQ)
# polys in t (b=1): W per orbit, Q
t = [Fr(0), Fr(1)]
def P(*c):
    return trim([Fr(x) for x in c])
FLOWS = {
  'L0':  ({0: P(1), 1: P(1)}, P(6), P(0), 'L', [(Fr(1), Fr(2))], P(Fr(-4), 4)),
  'M0':  ({0: P(-2, 1), 2: P(-2, 1), 3: P(8, -3), 4: P(10, -4)}, sc(12, P(3, -1)), P(0), 'M', [(Fr(2), Fr(5, 2))], mul(P(0, 0), P(0)) ),
  'H0':  ({3: P(4), 4: P(3), 5: P(1)}, P(24), P(0), 'MH', [(Fr(5, 2), Fr(3)), (Fr(3), None)], sc(8, P(-1, 1))),
  'Lf':  ({1: P(2), 3: P(1)}, P(8), P(8), 'L', [(Fr(1), Fr(2))], sc(4, P(-1, 1))),
  'M1f': ({1: P(6, -2), 3: P(-1, 1)}, P(8), P(8), 'M', [(Fr(2), Fr(7, 3))], sc(4, mul(P(-1, 1), P(3, -1)))),
  'M23f': ({1: P(26, -10), 2: P(-14, 6), 3: P(12, -4)}, sc(4, P(11, -3)), sc(16, P(8, -3)), 'M', [(Fr(7, 3), Fr(13, 5))], sc(8, mul(P(-1, 1), P(3, -1)))),
  'M4f': ({5: P(-26, 10), 2: P(4), 3: P(4)}, sc(20, P(-1, 1)), sc(4, P(-11, 5)), 'M', [(Fr(13, 5), Fr(3))], sc(8, P(0, 1) and mul(P(0, 1), P(-1, 1)))),
  'Hf':  ({5: P(1), 2: P(1), 3: P(1)}, P(10), P(4), 'H', [(Fr(3), None)], sc(2, P(-1, 1))),
}
# M0 target Q*T = 4(3-t)(4-t)
FLOWS['M0'] = FLOWS['M0'][:5] + (sc(4, mul(P(3, -1), P(4, -1))),)
# M4f target Q*T = 8 (t-1)  [b=1]
FLOWS['M4f'] = FLOWS['M4f'][:5] + (sc(8, P(-1, 1)),)

def tab(j, k, tt):
    return states(SEQ[j])[k][tt]

def nonneg_on(p, lo, hi):
    if hi is None:
        p = trim(p)
        assert len(p) <= 3
        if len(p) == 3:
            # need p>=0 on [lo,inf): leading >=0 and ... check via shift
            pass
        # shift t = lo + s, need coefficients >= 0 (sufficient)
        # compute p(lo + s)
        q = [Fr(0)]
        for i, c in enumerate(p):
            q = add(q, sc(c, [Fr(1)] if i == 0 else (mul([lo, 1], [lo, 1]) if i == 2 else [lo, 1])))
        return all(c >= 0 for c in q)
    if len(trim(p)) <= 2:
        return ev(p, lo) >= 0 and ev(p, hi) >= 0
    return bernstein_ok(p, lo, hi)[0]

WDEG = {'L0': 0, 'M0': 1, 'H0': 0, 'Lf': 0, 'M1f': 1, 'M23f': 1, 'M4f': 1, 'Hf': 0}
allok = True
for name, (Wo, Q, E, regs, ranges, QT) in FLOWS.items():
    W = [Wo.get(OIDX[j], P(0)) for j in range(N)]
    # sum W = Q
    tot = [Fr(0)]
    for w in W:
        tot = add(tot, w)
    ok = tot == trim(Q)
    for ri, (lo, hi) in enumerate(ranges):
        reg = regs[ri] if len(regs) > 1 else regs
        # weights nonneg
        for w in W:
            ok &= nonneg_on(w, lo, hi)
        ok &= nonneg_on(Q, lo, hi) and (ev(Q, lo) > 0)
        # band: |sum W tab - Q m k/6| <= m E/6
        for k in range(7):
            for tt in range(4):
                m = n[tt]
                s = [Fr(0)]
                for j in range(N):
                    s = add(s, sc(tab(j, k, tt), W[j]))
                d = sub(s, sc(Fr(m * k, 6), Q))
                ok &= nonneg_on(sub(sc(Fr(m, 6), E), d), lo, hi) and nonneg_on(add(sc(Fr(m, 6), E), d), lo, hi)
        # objective
        for k in range(1, 6):
            s = [Fr(0)]
            for j in range(N):
                v = states(SEQ[j])[k]
                s = add(s, mul(W[j], cost_poly(v, reg)))
            good = nonneg_on(sub(QT, s), lo, hi)
            if not good:
                print("OBJ FAIL", name, reg, k, s, QT)
            ok &= good
    print(name, "ok" if ok else "FAILED")
    allok &= ok
print("ALL OK" if allok else "SOME FAILED")
# emit Lean
def vec(xs):
    return "![" + ", ".join(xs) + "]"
out = []
out.append("/-- The type sequences: " + ", ".join(SEQ) + ". -/")
out.append("def sq : Fin %d → Fin 6 → Fin 4 :=" % N)
out.append("  ![" + ",\n    ".join(vec([str(T2I[c]) for c in s]) for s in SEQ) + "]")
out.append("")
out.append("/-- Their prefix counts. -/")
out.append("def tq : Fin %d → Fin 7 → Fin 4 → ℕ :=" % N)
rows = []
for j in range(N):
    st = states(SEQ[j])
    rows.append(vec([vec([str(x) for x in st[k]]) for k in range(7)]))
out.append("  ![" + ",\n    ".join(rows) + "]")
out.append("")
for name, (Wo, Q, E, regs, ranges, QT) in FLOWS.items():
    W = [Wo.get(OIDX[j], P(0)) for j in range(N)]
    out.append(f"/-- Weight numerators of `{name}` (denominator `{fmt_hom(Q, WDEG[name])}`). -/")
    deg = WDEG[name]
    out.append(f"noncomputable def W_{name} (a b : ℝ) : Fin {N} → ℝ :=")
    out.append("  " + vec([fmt_hom(w, deg) if trim(w) != [0] else "0" for w in W]))
    out.append("")
open("flows_price.lean", "w").write("\n".join(out))
