#!/usr/bin/env python3
"""D6 priority A: remove the cap, and check the uncapped primal/dual programme.

THE FINDING THAT FORCES THIS. `B3_dual_mixture.py` certifies a value for
max over eta in [0, cap] of J(w_eta). The supervisor exhibited eta = 13/20 > cap
beating that certificate at (q, mu, h) = (8, 1/4, 1/10). If that is right, the cap is
not a legality constraint on the design at all -- it was a sufficient condition of the
old proof used to rule out d >= 2 -- and it has been cutting off the optimum. Step 1
below re-derives the counterexample independently and certifies its sign with the
charge bracket, so it is confirmed or refuted here rather than taken on trust.

THE ALGEBRA THAT REPLACES THE CAP. With g = 1-mu, c the pair charge, x = nu - mu, the
information against exchange distance d is G_d(eta,x) = A_d x^2 + 2 B_d x + C_d with

  D_d = c(1-eta)(q-1) + 2 eta (2q-d-2)
  A_d = (q-d) D_d / (2 c q (q-1))
  B_d = eta g d (q-d) / (c q (q-1))
  C_d = (1-eta) d mu^2/(2q) + eta g^2 d (q+d-2) / (c q (q-1))

and, profiling the nuisance over all of R,  P_d = C_d - B_d^2/A_d, which for d = q
degenerates correctly (A_q = B_q = 0, so P_q = C_q). The decisive identity is

  P_d - d P_1 = d eta g^2 (d-1) [c(1-eta)+4eta] [c(1-eta)(q-1)+2eta(q-2)]
                / (c q D_1 D_d)   >= 0,

which gives G_d >= P_d >= d P_1 >= P_1 with NO cap. Every one of these is checked here
against B1's own `general_poly` in exact rational arithmetic, over a wide sweep; the
run raises on the first mismatch.

THE UNCAPPED CANDIDATE. If the optimum uses both scalars and pairs then their payoffs
against the uniform single-swap alternative must be equal, S(delta) = P(delta), giving
  a_c = 4q-6-c(q-1),  b_c = 2 g^2 - c mu^2,
  delta* = b_c / (2g + sqrt(4 g^2 - a_c b_c)),
  eta*   = c(q-1) delta* / (2g - a_c delta*),   V* = S(delta*).
delta* and eta* are LOCATED numerically and then everything reported about them is
recomputed in exact rationals at a rounded rational delta, so no claim rests on a float.

THE FULL-QUERY DUAL. For every legal (s,t,b) the single-swap alternative at delta gives
  H_{s,t,b} = [delta^2 (t-b)^2 - 2 delta (t-b)(g+delta) M1 + (g+delta)^2 M2] / (2 r^z)
with r = s+t+b, M1 = t/q - s/(q+1), M2 = t/q + s/(q+1) - 2st/(q(q+1)). If
H_{s,t,b} <= V* for every legal query AND the three scalar classes, then for ANY cost
allocation w, inf_lambda I(w,lambda) <= E_{pi*}[I(w,.)] <= V*, so V* bounds the FULL
design space -- no ansatz is assumed WLOG.

WHAT THIS DOES NOT ESTABLISH
 - The factorisation identity is verified exactly on a sweep, not proved for all
   (q,d,eta,c). Formalising it is the next step and is not done here.
 - delta*, eta*, V* are computed per cell; no closed-form proof that 0 <= eta* <= 1 and
   0 <= delta* <= mu in general.
 - The full-query dual is checked at the rounded delta on the listed cells only.
 - Charge enclosures: 2^z uses the exact 2^(z*) = 2(g/mu)^2 identity; r^z for r != 2
   still goes through the z* bracket, so those are looser and the slack reported for
   them carries that width.

    .venv/bin/python scripts/D8_uncapped_design.py
"""
from __future__ import annotations

from fractions import Fraction as F
import importlib.util, itertools, json, math, sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
spec = importlib.util.spec_from_file_location(
    "b1", REPO / "scripts/B1_d6_width_transition_local.py")
b1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b1)
from certified_pow import enclose_zstar, enclose_charge, enclose_root


def charge2(g, mu, h, digits=40):
    """certified bracket for 2**(z*-h), using 2**(z*) = 2 (g/mu)**2 EXACTLY."""
    p_, n_ = h.numerator, h.denominator
    lo, hi = enclose_root(F(2) ** (-p_), 1, n_, digits)
    base = 2 * (g / mu) ** 2
    return base * lo, base * hi


def Dd(q, c, eta, d):  return c * (1 - eta) * (q - 1) + 2 * eta * (2 * q - d - 2)
def Ad(q, c, eta, d):  return F(q - d) * Dd(q, c, eta, d) / (2 * c * q * (q - 1))
def Bd(q, mu, c, eta, d):
    return eta * (1 - mu) * d * (q - d) / (c * q * (q - 1))
def Cd(q, mu, c, eta, d):
    g = 1 - mu
    return ((1 - eta) * d * mu * mu / (2 * q)
            + eta * g * g * d * (q + d - 2) / (c * q * (q - 1)))
def Pd(q, mu, c, eta, d):
    g = 1 - mu
    return (Cd(q, mu, c, eta, d)
            - 2 * eta ** 2 * g ** 2 * d ** 2 * (q - d)
              / (c * q * (q - 1) * Dd(q, c, eta, d)))


def part1():
    print("PART 1 -- the quadratic, the profile and the factorisation, exactly")
    nq = nid = 0
    worst = None
    for q in (3, 4, 5, 6, 8):
        for mu in (F(1, 4), F(1, 3), F(2, 5)):
            g = 1 - mu
            for c in (F(3), F(7, 2), F(18), F(37, 2)):
                for eta in (F(1, 5), F(1, 3), F(13, 20), F(9, 10), F(1)):
                    for d in range(1, q + 1):
                        A = Ad(q, c, eta, d); B = Bd(q, mu, c, eta, d)
                        C = Cd(q, mu, c, eta, d)
                        for x in (F(0), F(1, 7), F(-1, 5), F(3, 11), F(-2, 9)):
                            got = b1.general_poly(q, mu, eta, c, d, x)
                            want = A * x * x + 2 * B * x + C
                            nq += 1
                            if got != want:
                                raise AssertionError(
                                    f"A_d/B_d/C_d mismatch q={q} d={d} eta={eta} "
                                    f"c={c} x={x}: {got} vs {want}")
                        # profile over all of R
                        P = Pd(q, mu, c, eta, d)
                        if d < q:
                            if P != C - B * B / A:
                                raise AssertionError("P_d != C_d - B_d^2/A_d")
                        else:
                            if A != 0 or B != 0 or P != C:
                                raise AssertionError("d = q branch is wrong")
                        # the boxed identity
                        lhs = P - d * Pd(q, mu, c, eta, 1)
                        rhs = (d * eta * g * g * (d - 1)
                               * (c * (1 - eta) + 4 * eta)
                               * (c * (1 - eta) * (q - 1) + 2 * eta * (q - 2))
                               / (c * q * Dd(q, c, eta, 1) * Dd(q, c, eta, d)))
                        nid += 1
                        if lhs != rhs:
                            raise AssertionError(
                                f"factorisation FAILS q={q} d={d} eta={eta} c={c}: "
                                f"{lhs} vs {rhs}")
                        if lhs < 0:
                            raise AssertionError("P_d - d P_1 is negative")
                        if worst is None or lhs < worst[0]:
                            worst = (lhs, q, d, eta, c)
    print(f"   A_d, B_d, C_d reproduce general_poly on {nq} exact evaluations")
    print(f"   P_d = C_d - B_d^2/A_d (and the d = q branch) on every configuration")
    print(f"   the factorisation identity holds EXACTLY on {nid} configurations, and")
    print(f"   its value is never negative; the smallest is {float(worst[0]):.3e} at "
          f"q={worst[1]} d={worst[2]} eta={worst[3]} c={worst[4]}")
    return {"quadratic_evaluations": nq, "identity_configurations": nid,
            "min_gap_float": float(worst[0])}


def Sdelta(q, mu, delta): return (mu * mu + (q - 1) * delta * delta) / (2 * q)
def Pdelta(q, mu, c, delta):
    g = 1 - mu
    return (g * g - 2 * g * delta + (2 * q - 3) * delta * delta) / (q * c)


def candidate(q, mu, c):
    """delta*, eta*, V* from the equal-payoff condition. Located in float, then the
    quantities are recomputed exactly at a rounded rational delta."""
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


def full_query_dual(q, mu, delta, zlo, zhi, h=None):
    """max over EVERY legal query of the single-swap payoff at nuisance mu - delta.
    Each charge r^z is replaced by a certified LOWER bound, which can only raise the
    payoff, so the maximum returned is a valid ceiling."""
    g = 1 - mu
    nu = mu - delta
    vals = [(nu * nu / (2 * (q + 1)), ("scalar", "A")),
            (Sdelta(q, mu, delta), ("scalar", "B")),
            (delta * delta / 2, ("scalar", "j"))]
    for s in range(q + 2):
        for t in range(q + 1):
            if not (1 <= s + t <= q):
                continue
            for bsw in (0, 1):
                if bsw == 0 and s + t < 2:
                    continue
                r = s + t + bsw
                m = t - bsw
                M1 = F(t, q) - F(s, q + 1)
                M2 = F(t, q) + F(s, q + 1) - 2 * F(s * t, q * (q + 1))
                E = (delta * delta * m * m
                     - 2 * delta * m * (g + delta) * M1
                     + (g + delta) ** 2 * M2)
                if r == 2 and h is not None:
                    # 2**(z*) = 2 (g/mu)**2 is EXACT, so the pair charge needs only a
                    # cheap n-th root and never the z* bracket. This matters: the pair
                    # is the query that binds, and routing it through the loose z*
                    # bracket was adding a uniform 1.733e-5 of spurious slack.
                    cr, _ = charge2(g, mu, h)
                else:
                    cr, _ = enclose_charge(r, zlo, zhi)
                vals.append((E / (2 * cr), ("query", s, t, bsw)))
    return max(vals), vals


def part2():
    print("\nPART 2 -- does the cap cut off the optimum?")
    out = []
    B3 = json.loads((REPO / "research/worker_gopB_20260913"
                     / "B3_dual_mixture.json").read_text())["rows"]
    for q, mu, h in ((8, F(1, 4), F(1, 10)), (4, F(1, 4), F(1, 10)),
                     (3, F(1, 4), F(1, 10)), (8, F(2, 5), F(1, 10))):
        g = 1 - mu
        cl, ch = charge2(g, mu, h)
        cstar = 2 * g * g / (mu * mu)
        cap = cl / (cl + cstar)
        row = [r for r in B3 if r["q"] == q and r["mu"] == str(mu)
               and r["h"] == str(h)][0]
        U = F(row["U_tight"])
        # primal at the UNCAPPED candidate eta*, plus the supervisor's 13/20, with the
        # charge UPPER bound => a valid lower bound. Using a fixed list of etas would
        # not be a test of the cap at all; eta* is where the uncapped optimum actually
        # sits, so that is what must be compared.
        cand = candidate(q, mu, cl)
        etas = [F(13, 20), F(3, 5), F(7, 10)]
        if cand is not None:
            etas.append(cand[1])
        best = None
        for eta in etas:
            if not (0 < eta <= 1):
                continue
            val = min(b1.profile_exact(q, mu, eta, ch, d)[0] for d in range(1, q + 1))
            if best is None or val > best[0]:
                best = (val, eta)
        L, eta_c = best
        beats = L > U
        eta_opt = None if cand is None else cand[1]
        print(f"   q={q} mu={mu} h={h}: cap = {float(cap):.9f}"
              + (f"   eta* = {float(eta_opt):.9f}"
                 f"{'  (ABOVE cap)' if eta_opt > cap else '  (inside cap)'}"
                 if eta_opt is not None else ""))
        print(f"      B3 certifies  max_(eta<=cap) J <= {float(U):.15f}")
        print(f"      eta = {eta_c} (> cap) gives J >= {float(L):.15f}")
        print(f"      L - U = {float(L - U):+.4e}   -> cap "
              f"{'CUTS OFF THE OPTIMUM' if beats else 'is not refuted here'}")
        out.append({"q": q, "mu": str(mu), "h": str(h), "cap": float(cap),
                    "U_capped": str(U), "eta_used": str(eta_c),
                    "L_uncapped": str(L), "L_minus_U": float(L - U),
                    "cap_cuts_optimum": bool(beats),
                    "eta_star": None if cand is None else str(cand[1]),
                    "eta_star_above_cap": None if cand is None
                                          else bool(cand[1] > cap)})
    return out


def main():
    res = {"part1": part1(), "part2": part2()}

    print("\nPART 3-4 -- the uncapped candidate, and a dual over EVERY legal query")
    rows = []
    for q in (3, 4, 5, 8):
        for mu in (F(1, 4), F(2, 5)):
            h = F(1, 10)
            g = 1 - mu
            cl, ch = charge2(g, mu, h)
            cstar = 2 * g * g / (mu * mu)
            cap = cl / (cl + cstar)
            zs_lo, zs_hi = enclose_zstar(g, mu)
            zlo, zhi = zs_lo - h, zs_hi - h
            cand = candidate(q, mu, cl)
            if cand is None:
                print(f"   q={q} mu={mu}: no real equal-payoff root; skipped")
                continue
            delta, eta, Sv, Pv = cand
            # primal at eta, certified with the charge UPPER bound
            Lval = min(b1.profile_exact(q, mu, eta, ch, d)[0] for d in range(1, q + 1))
            (U, arg), vals = full_query_dual(q, mu, delta, zlo, zhi, h)
            ok = U >= Lval
            rel = float((U - Lval) / Lval)
            print(f"   q={q} mu={mu}: delta*={float(delta):.9f} eta*={float(eta):.9f}"
                  f" (cap {float(cap):.6f}{', ABOVE cap' if eta > cap else ''})")
            print(f"      V* = S(delta*) = {float(Sv):.12f}   P(delta*) = "
                  f"{float(Pv):.12f}   |S-P| = {float(abs(Sv - Pv)):.2e}")
            print(f"      primal J(w_eta*) >= {float(Lval):.12f}")
            print(f"      FULL-QUERY dual  <= {float(U):.12f}   at {arg}")
            print(f"      relative gap {rel:.3e}   sandwich valid: {ok}")
            if not ok:
                raise AssertionError(f"full-query dual fell BELOW the primal at "
                                     f"q={q} mu={mu}")
            # DEFECT FIXED: these were only RECORDED as booleans. A value computed
            # at an eta outside [0,1] or a delta outside [0,mu] is not a certificate
            # for anything, so the cell is now REJECTED rather than reported.
            if not (0 <= eta <= 1):
                raise AssertionError(f"q={q} mu={mu}: eta* = {float(eta)} is outside "
                                     f"[0,1]; the cell is not a valid design")
            if not (0 <= delta <= mu):
                raise AssertionError(f"q={q} mu={mu}: delta* = {float(delta)} is "
                                     f"outside [0,mu]; the alternative is not legal")
            rows.append({"q": q, "mu": str(mu), "h": str(h),
                         "delta_star": str(delta), "eta_star": str(eta),
                         "cap": str(cap), "eta_above_cap": bool(eta > cap),
                         "eta_in_unit": bool(0 <= eta <= 1),
                         "delta_le_mu": bool(0 <= delta <= mu),
                         "V_star_S": str(Sv), "V_star_P": str(Pv),
                         "primal_L": str(Lval), "full_query_dual_U": str(U),
                         "dual_argmax": list(map(str, arg)),
                         "relative_gap": rel})
    res["uncapped"] = rows

    print("\nPART 5c -- slack at the boundary z = z*, delta = 0")
    sl = []
    for q in (3, 4, 5, 8):
        for mu in (F(1, 4), F(2, 5)):
            g = 1 - mu
            zs_lo, zs_hi = enclose_zstar(g, mu)
            (U, arg), vals = full_query_dual(q, mu, F(0), zs_lo, zs_hi, F(0))
            V0 = mu * mu / (2 * q)
            # DEFECT FIXED: the active classes used to be selected by `v != V0`. Every
            # `v` here is an UPPER enclosure, so the B-pair -- which is EXACTLY V0 --
            # can come out a shade larger and be misclassified as inactive, which then
            # reports a negative slack. The active set is a property of the MODEL, so
            # it is now named by class identity.
            ACTIVE = {("scalar", "B"), ("query", 0, 2, 0)}
            tied = [a for v, a in vals if a in ACTIVE]
            nz = [(V0 - v) / V0 for v, a in vals if a not in ACTIVE]
            slack = min(nz) if nz else F(0)
            # the active classes must still land on V0 to within the enclosure width
            for v, a in vals:
                if a in ACTIVE and abs(v - V0) > V0 * F(1, 10 ** 6):
                    raise AssertionError(f"q={q} mu={mu}: class {a} was expected to "
                                         f"tie V0 but is off by {float(v - V0):.3e}")
            # CERTIFIED bound: (2/3)^(z*-1) is irrational, so it needs an enclosure.
            # x |-> (2/3)^x is DECREASING, so an UPPER bound on it comes from the
            # LOWER endpoint of the z bracket, giving a valid LOWER bound on
            # 1 - (2/3)^(z*-1).
            e_lo = zs_lo - 1
            _, pow_hi = enclose_root(F(2, 3), e_lo.numerator, e_lo.denominator, 40)
            bound = min(F(1, q + 1), 1 - pow_hi)
            print(f"   q={q} mu={mu}: V0 = {float(V0):.9f}, classes AT V0: "
                  f"{len(tied)} {tied[:3]}")
            print(f"      smallest normalised slack among the rest: {float(slack):.6f}"
                  f"   (proposed lower bound {float(bound):.6f})")
            sl.append({"q": q, "mu": str(mu), "V0": str(V0),
                       "tied_classes": [list(map(str, a)) for a in tied],
                       "min_normalised_slack": float(slack),
                       "proposed_bound": float(bound),
                       "proposed_bound_exact": str(bound),
                       "power_enclosure_upper": str(pow_hi),
                       "bound_holds": bool(slack >= bound)})
    res["boundary_slack"] = sl
    nb = sum(1 for r in sl if not r["bound_holds"])
    print(f"   the proposed bound min(1/(q+1), 1-(2/3)^(z*-1)) holds in "
          f"{len(sl)-nb}/{len(sl)} cells")

    res["not_established"] = [
        "the factorisation identity is verified exactly on a sweep, not proved for "
        "all (q, d, eta, c); formalising it is the next step",
        "no closed-form proof that 0 <= eta* <= 1 and 0 <= delta* <= mu in general",
        "the full-query dual is checked at a rounded rational delta on the listed "
        "cells only",
        "r^z for r != 2 still goes through the z* bracket and is looser than the "
        "exact 2^(z*) = 2(g/mu)^2 route used for r = 2",
    ]
    out = REPO / "research/worker_D8_uncapped_20260914/D8_uncapped_design.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
