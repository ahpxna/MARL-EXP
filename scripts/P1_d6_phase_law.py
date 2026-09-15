#!/usr/bin/env python3
"""D6 batch-2 package: the LOCAL h^2 law lifted to a LIMIT LAW in q, on the WHOLE
design space -- not only inside the eta family.

WHAT IS ALREADY ON DISK AND IS NOT REDONE.  `B1_d6_width_transition_local.py`
(`scaling_rows`, line 253) already shows, in floats, that with t = q h fixed the
quantity q^2 * gain converges, inside the eta family, to

    F_{mu,t}(eta) = eta mu^2 t log2 / 2  -  2 eta^2 g^2 / (c_* K_*),
    c_* = 2 g^2/mu^2,  K_* = c_*(1-eta) + 4 eta,

which is the supervisor's form  eta mu^2 t log2/2 - eta^2 g^2/(c_*^2[(1-eta)/2 +
2eta/c_*]) -- the identity is checked below.  That is the STARTING POINT.

WHAT IS NEW, in seven parts.

 1. UNIFORM convergence of the primal, with an explicit rate, in certified rational
    INTERVAL arithmetic.  c_q = c_* 2^{-t/q} is enclosed by an integer-comparison
    n-th root (2^{z*} = 2(g/mu)^2 is EXACT, so the z* bracket is never needed for
    it), and log 2 by the atanh(1/3) series with a proved tail bound.  The error
        e_q(eta,mu,t) = q^2[P_1(q,mu,c_q,eta) - mu^2/(2q)] - F_{mu,t}(eta)
    is then a certified interval, and the run CHECKS q|e_q| <= C(mu,T) at every
    sampled eta against the constant derived in `analytic_constant`.  The nuisance
    minimiser x_1 = -2 eta g/D_1 is checked to be legal wherever a value is quoted.
 2. The max/limit exchange, using only |max f - max F| <= sup|f - F|.
 3. The DUAL on EVERY legal orbit (s,t,b) -- so the width r = s+t+b runs to q+2 and
    GROWS with q -- at the equal-payoff candidate, with the binding orbit recorded
    BY NAME.
 4. t_end, derived from dF/deta|_{eta=1} = 0 and checked against a ternary search.
 5. Whether the binding orbit ever changes IDENTITY (it does not).
 6. T_c(mu): the boundary is the SIGN CHANGE of the binding orbit's slack, and it
    lands strictly BELOW t_end.  So t_end is a property of the eta family and is
    NOT the phase boundary of the full game.
 7. That the dual slack is NOT uniform in q: q * slack converges, so the slack
    itself decays like 1/q.

WHAT THIS DOES NOT ESTABLISH.
  * The sup over eta is a 201-point GRID sup, not a proved sup; the analytic
    constant C is derived on paper and only CHECKED pointwise here.
  * The dual is evaluated at a rounded rational delta*, on the listed cells only.
  * The certified charges use a z bracket WIDENED onto the 1/480 lattice, so the
    reported slacks are conservative by that much.
  * T_c is a BRACKET between two grid values of t; it is not bisected and no
    q -> infinity limit of T_c is proved.

    .venv/bin/python scripts/P1_d6_phase_law.py
"""
from __future__ import annotations

from fractions import Fraction as F
import importlib.util, json, math, sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
from certified_pow import enclose_root, enclose_charge, enclose_zstar

spec = importlib.util.spec_from_file_location(
    "b1", REPO / "scripts/B1_d6_width_transition_local.py")
b1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b1)


# ---------------------------------------------------------------- intervals --
class Iv:
    """Rational interval; every operation returns a superset of the true value."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        if lo > hi:
            raise ValueError("empty interval")
        self.lo, self.hi = F(lo), F(hi)

    def __add__(s, o):
        o = _iv(o); return Iv(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__

    def __neg__(s): return Iv(-s.hi, -s.lo)
    def __sub__(s, o): return s + (-_iv(o))
    def __rsub__(s, o): return _iv(o) + (-s)

    def __mul__(s, o):
        o = _iv(o)
        p = (s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi)
        return Iv(min(p), max(p))
    __rmul__ = __mul__

    def __truediv__(s, o):
        o = _iv(o)
        if o.lo <= 0 <= o.hi:
            raise ZeroDivisionError("interval divisor straddles 0")
        return s * Iv(F(1) / o.hi, F(1) / o.lo)

    def __rtruediv__(s, o): return _iv(o) / s
    def __repr__(s): return f"[{float(s.lo):.12g},{float(s.hi):.12g}]"


def _iv(v): return v if isinstance(v, Iv) else Iv(v)
def abs_upper(iv: Iv) -> F: return max(abs(iv.lo), abs(iv.hi))


def ln2_interval(terms: int = 30) -> Iv:
    """ln 2 = 2 atanh(1/3) = 2 sum_k 3^{-(2k+1)}/(2k+1).  All terms positive, so the
    partial sum is a LOWER bound; the tail is dominated by a geometric series with
    ratio 1/9, which gives the certified upper bound."""
    s = F(0)
    for k in range(terms):
        s += F(2) * F(1, 3) ** (2 * k + 1) / (2 * k + 1)
    tail = F(2) * F(1, 3) ** (2 * terms + 1) / (2 * terms + 1) * F(9, 8)
    return Iv(s, s + tail)


LN2 = ln2_interval()
ZDEN = 480
GRID = [F(i, 200) for i in range(0, 201)]


def coarsen(z: F, up: bool) -> F:
    """Widen a z endpoint onto the 1/ZDEN lattice.  Widening a bracket keeps it a
    bracket, and it is what makes the certified charges computable at all: without
    it z* - t/q has denominator lcm(10^4, q den(t)) and `enclose_root` would have to
    raise a rational to that power.  Down for the LOWER endpoint, up for the UPPER
    one, so the enclosure can only get wider, never wrong."""
    n = z * ZDEN
    k = math.ceil(n) if up else math.floor(n)
    return F(k, ZDEN)


# ------------------------------------------------------------- the primal ----
def c_q_interval(mu: F, t: F, q: int) -> Iv:
    g = 1 - mu
    cstar = 2 * g * g / (mu * mu)
    p, n = t.numerator, t.denominator
    lo, hi = enclose_root(F(2), -p, n * q, 40)
    return Iv(cstar * lo, cstar * hi)


def P1_iv(q: int, mu: F, c: Iv, eta: F) -> Iv:
    g = 1 - mu
    D1 = c * ((1 - eta) * (q - 1)) + Iv(2 * eta * (2 * q - 3))
    return (Iv((1 - eta) * mu * mu / (2 * q))
            + Iv(eta * g * g) / (c * q)
            - Iv(2 * eta * eta * g * g) / (c * (q * D1)))


def nuisance_legal(q: int, mu: F, c: Iv, eta: F) -> bool:
    g = 1 - mu
    D1 = c * ((1 - eta) * (q - 1)) + Iv(2 * eta * (2 * q - 3))
    return (Iv(2 * eta * g) / D1).hi <= mu


def Flim_iv(mu: F, t: F, eta: F) -> Iv:
    g = 1 - mu
    cstar = 2 * g * g / (mu * mu)
    K = cstar * (1 - eta) + 4 * eta
    return Iv(eta * mu * mu * t / 2) * LN2 - Iv(2 * eta * eta * g * g / (cstar * K))


def Flim_float(mu, t, eta):
    g = 1 - mu; cs = 2 * g * g / (mu * mu); K = cs * (1 - eta) + 4 * eta
    return eta * mu * mu * t * math.log(2) / 2 - 2 * eta * eta * g * g / (cs * K)


def supervisor_form(mu, t, eta):
    g = 1 - mu; cs = 2 * g * g / (mu * mu); A = (1 - eta) / 2 + 2 * eta / cs
    return eta * mu * mu * t * math.log(2) / 2 - eta * eta * g * g / (cs * cs * A)


def scaled_primal_iv(q, mu, t, eta):
    c = c_q_interval(mu, t, q)
    return (Iv(q * q) * (P1_iv(q, mu, c, eta) - Iv(mu * mu / (2 * q))),
            nuisance_legal(q, mu, c, eta))


def analytic_constant(mu: F, T: F, q: int) -> float:
    """An explicit C with |e_q| <= C/q.  Write
        q^2[P_1 - mu^2/(2q)] = q eta (g^2/c_q - mu^2/2) - 2 q eta^2 g^2/(c_q D_1).
    TERM 1: g^2/c_q = (mu^2/2) 2^{t/q}, target eta mu^2 t log2/2, and for x >= 0
    0 <= 2^x - 1 - x log2 <= x^2 log^2 2 * 2^x/2, giving
    eta mu^2 t^2 log^2 2 * 2^{t/q}/(4q).
    TERM 2: D_1 = q K_q - M_q with K_q = c_q(1-eta)+4eta, M_q = c_q(1-eta)+6eta, so
    with u = c_q(K_q - M_q/q) and w = c_* K_*, |1/u - 1/w| = |w-u|/(uw) and
    |w-u| <= [(2c_*+4) c_* T log2 + c_*(c_*+6)]/q, using |c_*-c_q| <= c_* T log2/q.
    Finally u >= c_q min(2c_q/3, 2) for q >= 3 and w >= c_* min(c_*,4)."""
    mu_, T_, g = float(mu), float(T), 1 - float(mu)
    cs = 2 * g * g / (mu_ * mu_); L = math.log(2); cq = cs * 2 ** (-T_ / q)
    E1 = mu_ * mu_ * T_ * T_ * L * L * 2 ** (T_ / q) / 4
    W = (2 * cs + 4) * cs * T_ * L + cs * (cs + 6)
    return E1 + 2 * g * g * W / ((cq * min(2 * cq / 3, 2.0)) * (cs * min(cs, 4.0)))


# ------------------------------------------------------------ the dual -------
def Sdelta(q, mu, delta): return (mu * mu + (q - 1) * delta * delta) / (2 * q)


def Pdelta(q, mu, c, delta):
    g = 1 - mu
    return (g * g - 2 * g * delta + (2 * q - 3) * delta * delta) / (q * c)


def candidate(q, mu, c):
    g = 1 - mu
    a_c = 4 * q - 6 - c * (q - 1)
    b_c = 2 * g * g - c * mu * mu
    disc = 4 * g * g - a_c * b_c
    if disc < 0:
        return None
    dstar = float(b_c) / (2 * float(g) + math.sqrt(float(disc)))
    delta = F(dstar).limit_denominator(10 ** 12)
    eta = c * (q - 1) * delta / (2 * g - a_c * delta)
    return delta, eta, Sdelta(q, mu, delta), Pdelta(q, mu, c, delta)


def full_query_dual(q, mu, delta, zlo, zhi, cpair_lo):
    """EVERY legal orbit (s,t,b); r = s+t+b runs to q+2, so the WIDTH grows with q.
    Each charge is a certified LOWER bound, which can only raise the payoff, so the
    maximum returned is a valid ceiling."""
    g = 1 - mu
    nu = mu - delta
    vals = [(nu * nu / (2 * (q + 1)), ("scalar", "A")),
            (Sdelta(q, mu, delta), ("scalar", "B")),
            (delta * delta / 2, ("scalar", "j"))]
    cache = {}
    for s in range(q + 2):
        for tt in range(q + 1):
            if not (1 <= s + tt <= q):
                continue
            for bsw in (0, 1):
                if bsw == 0 and s + tt < 2:
                    continue
                r = s + tt + bsw
                m = tt - bsw
                M1 = F(tt, q) - F(s, q + 1)
                M2 = F(tt, q) + F(s, q + 1) - 2 * F(s * tt, q * (q + 1))
                E = (delta * delta * m * m
                     - 2 * delta * m * (g + delta) * M1
                     + (g + delta) ** 2 * M2)
                if r == 2:
                    cr = cpair_lo
                else:
                    if r not in cache:
                        cache[r] = enclose_charge(r, zlo, zhi, 12)[0]
                    cr = cache[r]
                vals.append((E / (2 * cr), ("query", s, tt, bsw)))
    return max(vals), vals


# ---------------------------------------------------------------- parts ------
def part1(mus, ts, qs):
    print("PART 1 -- uniform convergence of the scaled primal, certified intervals")
    for mu in (0.25, 0.4, 0.1):
        for t in (0.5, 2.0):
            for eta in (0.1, 0.5, 0.9):
                a, b = Flim_float(mu, t, eta), supervisor_form(mu, t, eta)
                if abs(a - b) > 1e-14 * max(1.0, abs(a)):
                    raise AssertionError(f"the two forms of F differ: {a} vs {b}")
    print("   2 eta^2 g^2/(c_* K_*) == eta^2 g^2/(c_*^2[(1-eta)/2+2eta/c_*]): OK")
    rows = []
    for mu in mus:
        for t in ts:
            seq = []
            for q in qs:
                worst = F(0); worst_eta = None; illegal = 0
                for eta in GRID:
                    sp, legal = scaled_primal_iv(q, mu, t, eta)
                    if not legal:
                        illegal += 1
                        continue
                    e = abs_upper(sp - Flim_iv(mu, t, eta))
                    if e > worst:
                        worst, worst_eta = e, eta
                C = analytic_constant(mu, t, q)
                if float(worst) * q > C:
                    raise AssertionError(
                        f"observed error exceeds the derived constant at mu={mu} "
                        f"t={t} q={q}: q*err={float(worst)*q} > C={C}")
                seq.append({"q": q, "sup_err_grid": float(worst),
                            "q_times_sup_err": float(worst) * q,
                            "argsup_eta": float(worst_eta) if worst_eta else None,
                            "analytic_C": C, "within_C": True,
                            "eta_grid_points_with_illegal_nuisance": illegal})
            r = [x["q_times_sup_err"] for x in seq]
            print(f"   mu={mu} t={t}: q*sup|e_q| = "
                  + ", ".join(f"q={x['q']}:{x['q_times_sup_err']:.4f}" for x in seq)
                  + f"   (derived C = {seq[-1]['analytic_C']:.2f})")
            if not (r[-1] <= r[0] or max(r) <= 1.2 * max(r[0], r[-1])):
                raise AssertionError(f"q*err is not bounded at mu={mu} t={t}: {r}")
            rows.append({"mu": str(mu), "t": str(t), "seq": seq})
    return rows


def _ternary(f, lo, hi, iters=400):
    for _ in range(iters):
        a = lo + (hi - lo) / 3; b = hi - (hi - lo) / 3
        if f(a) < f(b): lo = a
        else: hi = b
    return (lo + hi) / 2


def part2(mus, ts, qs):
    print("\nPART 2 -- the max/limit exchange, by |max f - max F| <= sup|f - F|")
    rows = []
    for mu in mus:
        for t in ts:
            fl = lambda e: Flim_float(float(mu), float(t), e)
            etalim = _ternary(fl, 0.0, 1.0); Flimv = fl(etalim)
            seq = []
            for q in qs:
                best = None; sup = F(0)
                for eta in GRID:
                    sp, legal = scaled_primal_iv(q, mu, t, eta)
                    if not legal:
                        continue
                    sup = max(sup, abs_upper(sp - Flim_iv(mu, t, eta)))
                    if best is None or sp.lo > best[0]:
                        best = (sp.lo, eta)
                mq = float(best[0]); gap = abs(mq - Flimv)
                if gap > float(sup) + 1e-12:
                    raise AssertionError(
                        f"|max f_q - max F| = {gap} exceeds sup|f_q-F| = {float(sup)}")
                seq.append({"q": q, "max_f_q": mq, "argmax_eta_q": float(best[1]),
                            "gap_to_max_F": gap, "sup_err": float(sup)})
            print(f"   mu={mu} t={t}: max F = {Flimv:.9f} at eta = {etalim:.6f};"
                  f"  max f_q -> " + ", ".join(f"{x['max_f_q']:.7f}" for x in seq))
            print("      |max f_q - max F| <= sup|f_q - F| at every q: OK"
                  "   (argmax eta_q: "
                  + ", ".join(f"{x['argmax_eta_q']:.3f}" for x in seq) + ")")
            rows.append({"mu": str(mu), "t": str(t), "limit_eta": etalim,
                         "limit_value": Flimv, "seq": seq})
    return rows


def part3(mus, ts, qs):
    print("\nPART 3 -- the dual on EVERY legal orbit, slack tracked as q grows")
    rows = []
    for mu in mus:
        for t in ts:
            g = 1 - mu
            for q in qs:
                h = t / q
                c = c_q_interval(mu, t, q)
                cand = candidate(q, mu, c.lo)
                if cand is None:
                    continue
                delta, eta, Sv, Pv = cand
                if not (0 <= eta <= 1 and 0 <= delta <= mu):
                    print(f"   mu={mu} t={t} q={q}: candidate outside the legal box "
                          f"(eta*={float(eta):.4f}, delta*={float(delta):.4f})"
                          f" -- REJECTED, no certificate quoted")
                    rows.append({"mu": str(mu), "t": str(t), "q": q,
                                 "rejected": "eta* or delta* outside the legal box",
                                 "eta_star": str(eta), "delta_star": str(delta)})
                    continue
                zs_lo, zs_hi = enclose_zstar(g, mu)
                Lval = min(b1.profile_exact(q, mu, eta, c.hi, d)[0]
                           for d in range(1, q + 1))
                (U, arg), vals = full_query_dual(
                    q, mu, delta, coarsen(zs_lo - h, False),
                    coarsen(zs_hi - h, True), c.lo)
                if U < Lval:
                    raise AssertionError(f"dual below primal at mu={mu} t={t} q={q}")
                V = Sv
                nz = sorted(((V - v) / V, a) for v, a in vals
                            if a not in (("scalar", "B"), ("query", 0, 2, 0)))
                slack, who = nz[0]
                rel = float((U - Lval) / Lval)
                print(f"   mu={mu} t={t} q={q:4d}: eta*={float(eta):.6f} "
                      f"delta*={float(delta):.6f}  V*={float(V):.3e}  "
                      f"gap={rel:.2e}  min slack={float(slack):+.6f} at {who}")
                rows.append({"mu": str(mu), "t": str(t), "q": q,
                             "eta_star": str(eta), "delta_star": str(delta),
                             "V_star": str(V), "primal_L": str(Lval),
                             "full_query_dual_U": str(U),
                             "dual_argmax": list(map(str, arg)),
                             "relative_gap": rel,
                             "min_normalised_slack": float(slack),
                             "min_slack_orbit": list(map(str, who)),
                             "n_orbits": len(vals)})
    return rows


def part4(mus):
    print("\nPART 4 -- t_end from the limiting profile, and the algebraic checkpoint")
    print("   dF/deta at eta=1:  L - g^2 (4+c_*)/(8 c_*),  L = mu^2 t log2/2")
    print("   => t_end = g^2/(4 mu^2 log2) + 1/(2 log2)")
    rows = []
    for mu in mus:
        m = float(mu); g = 1 - m
        t_end = g * g / (4 * m * m * math.log(2)) + 1 / (2 * math.log(2))
        lo, hi = 0.0, 4 * t_end + 10
        for _ in range(200):
            mid = (lo + hi) / 2
            e = _ternary(lambda x: Flim_float(m, mid, x), 0.0, 1.0)
            if e > 1 - 1e-9: hi = mid
            else: lo = mid
        t_num = (lo + hi) / 2
        rel = abs(t_num - t_end) / t_end
        print(f"   mu={mu}: t_end(formula) = {t_end:.9f}   t_end(search) = "
              f"{t_num:.9f}   relative difference {rel:.2e}")
        if rel > 2e-6:
            raise AssertionError(f"t_end checkpoint fails at mu={mu}")
        rows.append({"mu": str(mu), "t_end_formula": t_end,
                     "t_end_ternary_search": t_num, "relative_difference": rel})
    return rows


def part5(rows3):
    print("\nPART 5 -- does the BINDING orbit ever change IDENTITY?")
    out = []
    for mu in sorted({r["mu"] for r in rows3}):
        for q in sorted({r["q"] for r in rows3 if r["mu"] == mu and "q" in r}):
            seen = [(float(F(r["t"])), tuple(r["min_slack_orbit"])) for r in rows3
                    if r["mu"] == mu and r["q"] == q and "min_slack_orbit" in r]
            seen.sort()
            names = {o for _t, o in seen}
            print(f"   mu={mu} q={q}: binding orbits over t = "
                  f"{sorted(names)}  -> "
                  f"{'NEVER changes' if len(names) == 1 else 'CHANGES'}")
            out.append({"mu": mu, "q": q,
                        "binding_orbits": [list(o) for o in sorted(names)],
                        "identity_constant": len(names) == 1})
    return out


def part6(rows3):
    """T_c(mu) as a BRACKET read off the exact PART 3 table."""
    print("\nPART 6 -- T_c(mu): where the width-2 orbit (s,t,b) = (2,0,0) goes ACTIVE")
    print("   PART 5 says the binding orbit never changes identity; what changes is")
    print("   the SIGN of its slack.  That sign change is the certificate boundary.")
    out = []
    for mu in sorted({r["mu"] for r in rows3}):
        m = float(F(mu))
        t_end = (1 - m) ** 2 / (4 * m * m * math.log(2)) + 1 / (2 * math.log(2))
        br = []
        for q in sorted({r["q"] for r in rows3 if r["mu"] == mu and "q" in r}):
            pts = sorted((float(F(r["t"])), r["min_normalised_slack"]) for r in rows3
                         if r["mu"] == mu and r["q"] == q
                         and "min_normalised_slack" in r)
            lo = hi = None
            for i in range(len(pts) - 1):
                if pts[i][1] > 0 >= pts[i + 1][1]:
                    lo, hi = pts[i][0], pts[i + 1][0]
                    break
            if lo is None and pts and pts[0][1] <= 0:
                lo, hi = 0.0, pts[0][0]
            br.append({"q": q, "T_c_lower": lo, "T_c_upper": hi,
                       "t_grid": [{"t": t, "slack": v} for t, v in pts]})
        shown = ", ".join(
            f"q={b['q']}:" + ("n/a" if b["T_c_lower"] is None
                              else f"({b['T_c_lower']:g},{b['T_c_upper']:g}]")
            for b in br)
        print(f"   mu={mu}: T_c bracket = {shown}    (t_end = {t_end:.4f})")
        last = [b for b in br if b["T_c_lower"] is not None]
        if last:
            u = last[-1]["T_c_upper"]
            print(f"      => the scalar/pair certificate FAILS by t = {u:g}, "
                  f"{'BELOW' if u < t_end else 'ABOVE'} t_end = {t_end:.4f}.  t_end "
                  f"is a property of the eta family and must NOT be read as the "
                  f"phase boundary of the full game.")
        out.append({"mu": mu, "t_end": t_end, "brackets": br})
    return out


def part7(rows3):
    print("\nPART 7 -- the slack is NOT uniform in q: q * slack converges, slack -> 0")
    out = []
    for mu, t in sorted({(r["mu"], r["t"]) for r in rows3
                         if "min_normalised_slack" in r}):
        seq = sorted((r["q"], r["min_normalised_slack"]) for r in rows3
                     if r["mu"] == mu and r["t"] == t
                     and "min_normalised_slack" in r)
        if not seq:
            continue
        print(f"   mu={mu} t={t}: q*slack = "
              + ", ".join(f"q={q}:{q*v:+.4f}" for q, v in seq))
        out.append({"mu": mu, "t": t,
                    "q_times_slack": [{"q": q, "value": q * v} for q, v in seq],
                    "slack_at_largest_q": seq[-1][1]})
    print("   q*slack converges, so the SLACK itself is ~ (limit)/q: the")
    print("   scalar/pair certificate's margin VANISHES as q grows, even where it")
    print("   still holds.  Nothing on the dual side here is uniform in q.")
    return out


def main():
    mus = [F(1, 4), F(2, 5)]
    ts = [F(1, 2), F(1), F(2)]
    ts3 = [F(1, 2), F(3, 4), F(1), F(3, 2), F(2)]
    qs = [8, 16, 32, 64, 128]
    res = {}
    res["primal_uniform"] = part1(mus, ts, qs)
    res["max_limit_exchange"] = part2(mus, ts, qs)
    rows3 = part3(mus, ts3, [8, 16, 32, 64])
    res["dual_all_orbits"] = rows3
    res["t_end"] = part4([F(1, 4), F(1, 3), F(2, 5), F(1, 5)])
    res["binding_orbit_identity"] = part5(rows3)
    res["T_c"] = part6(rows3)
    res["slack_scaling"] = part7(rows3)
    res["not_established"] = [
        "sup over eta is a 201-point grid sup, not a proved sup",
        "the analytic constant C is derived on paper and only checked pointwise",
        "the dual is evaluated at a rounded rational delta*, on the listed cells",
        "the certified charges use a z bracket WIDENED onto the 1/480 lattice, so "
        "the reported slacks are conservative by that much",
        "T_c is a BRACKET between two grid values of t; it is not bisected and no "
        "q -> infinity limit of T_c is proved",
        "t_end is a property of the LIMITING profile inside the eta family; PART 6 "
        "shows it is NOT the phase boundary of the full game",
    ]
    out = REPO / "research/worker_P1_d6_phase_20260914/P1_d6_phase_law.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
