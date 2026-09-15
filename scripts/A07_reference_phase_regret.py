#!/usr/bin/env python3
"""
A07 probe 2: TRUE plug-in decision regret on the actual phase value formula
`phaseValueFull`, at the D6 reference instance.  EXACT rational arithmetic
(fractions.Fraction) throughout -- no floating point decides anything.

Transcribed literally from:
  work/p13_conjectures/LeanD6ReferencePhaseValueV1.lean
      base, risk0, riskOne, riskGen, mixRisk, uOne, vTerm, uTop,
      phaseValue, phaseValueFull
  work/p13_conjectures/D6_REFERENCE_PHASE_DERIVATION_20260911.md
      c = (1-t)^(2k-2),  a = c(1+(k-2)t),  b = c(k-2)t,
      p = rho-2b,  r = 2a-rho,  e = min(a,2b),  denominator c = a-b.

VARIABLES AND UNITS (the supervisor's warning, taken seriously):
  t     : the REFERENCE parameter (Bernoulli rate of the product reference).
          This is the statistical parameter being estimated here.  Errors
          `err` below are errors in t, dimensionless.
  rho   : the prescribed visible response slope, 1 <= rho <= 2.  Held fixed.
  qq    : the ALLOCATION/DECISION WEIGHT -- probability the decision rule puts
          on the action d=0.  qq lives in [0,1].  d/dqq is curvature in the
          DECISION, d/dt is curvature in the PARAMETER.  They are NEVER mixed:
          every constant below is labelled with which variable it differentiates.
  h     : the adversary's |A cap T|, an INTEGER in {1,...,k}.  Because the inner
          maximum is over a DISCRETE set, risk is PIECEWISE LINEAR in qq.  This
          is the structural reason the answer here differs from the D6
          phase-III oracle (probe 1), whose inner optimisation is over a
          CONTINUOUS nuisance u and is therefore quadratic.

Run:  python3 scripts/A07_reference_phase_regret.py
"""
import json
from fractions import Fraction as F

# ------------------------------------------------------------------ instance

def slopes(k, t, rho):
    """Closed forms of the D6 reference instance.  All exact rationals."""
    c = (1 - t) ** (2 * k - 2)
    a = c * (1 + (k - 2) * t)
    b = c * (k - 2) * t
    p = rho - 2 * b
    r = 2 * a - rho
    e = min(a, 2 * b)
    return dict(a=a, b=b, c=c, p=p, r=r, e=e, cden=a - b)

# --------------------------------------------- Lean definitions, transcribed

def pos(x):                 return x if x > 0 else F(0)          # max 0 x
def uOne(r, e):             return pos(r - e) / 2
def vTerm(k, p, e, r):      return (p * (k - 1) + pos(e - r)) / 2
def uTop(k, r, e):          return (k * r - e) / 2
def phaseValueFull(k, p, c, e, r):
    return pos(k * r - e) * (p * (k - 1) + pos(e - r)) / (4 * (c * (k - 1)))

def base(k, p, c, e, r, h, d):  return (p * d - 2 * c * (h * d / F(k)) + max(e, r * h)) / 2
def risk0(e, r, h):             return (max(e, r * h) - e) / 2
def riskOne(k, p, c, e, r, b, h): return base(k, p, c, e, r, h, F(1)) - b * (k - h) / F(k) / 2
def riskGen(k, p, c, e, r, h, d): return base(k, p, c, e, r, h, d)
def mixRisk(k, p, c, e, r, q, h): return q * risk0(e, r, h) + (1 - q) * base(k, p, c, e, r, h, F(k))

# ------------------------------------------------- the 2x2 reduced game at t

def game(k, t, rho):
    """Returns the 2x2 payoff rows, the optimal decision weight qq* on d=0,
    and the minimax value.  Active case only unless kr<=e (then qq*=1, V=0)."""
    s = slopes(k, t, rho)
    p, r, e, cd = s["p"], s["r"], s["e"], s["cden"]
    U, u0, v = uTop(k, r, e), uOne(r, e), vTerm(k, p, e, r)
    D = cd * (k - 1)
    active = (k * r - e) > 0
    if active:
        q = v / D                       # phase_equalizers: primal weight on d=0
        q = min(max(q, F(0)), F(1))
    else:
        q = F(1)
    V = phaseValueFull(k, p, cd, e, r)
    return dict(s=s, U=U, u0=u0, v=v, D=D, qstar=q, V=V, active=active)

def risk_at(g, q):
    """max over the two endpoint worlds h in {1,k} of the mixture risk.
       Row h=1 : q*u0 + (1-q)*v      Row h=k : q*U + (1-q)*0"""
    return max(g["u0"] * q + g["v"] * (1 - q), g["U"] * q)

def true_regret(k, t, rho, that):
    """Plug-in decision regret: play the t-hat optimum, pay at the true t."""
    gt, gh = game(k, t, rho), game(k, that, rho)
    return risk_at(gt, gh["qstar"]) - gt["V"], gt, gh

# ---------------------------------------------------------------- self-check

def rho_crit(k, t):
    """k*r = e  <=>  rho = 2a - e/k.  Above it the value collapses to 0."""
    s = slopes(k, t, F(1))          # a,b,c,e do not depend on rho
    return 2 * s["a"] - s["e"] / k

print("=" * 78)
print("0. SELF-CHECKS (exact rationals)")
print("=" * 78)
bad_val, bad_dom, bad_suff = [], [], []
CHECK_K = [3, 4, 8, 16]
CHECK_T = [F(1, 200), F(1, 80), F(1, 20), F(1, 10), F(1, 6), F(1, 4), F(2, 5)]
CHECK_R = [F(1), F(5, 4), F(3, 2), F(15, 8), F(2)]
n_cells = n_suff = 0
for k in CHECK_K:
    for t in CHECK_T:
        for rho in CHECK_R:
            n_cells += 1
            g = game(k, t, rho)
            s = g["s"]
            suff = (k - 2) * s["b"] >= 1           # the sufficient regime
            if suff:
                n_suff += 1
            # (a) minimax of the 2x2 equals phaseValueFull, computed independently
            #     by scanning qq on an exact rational grid + the equalizer point
            cands = [F(i, 400) for i in range(401)] + [g["qstar"]]
            v_scan = min(risk_at(g, q) for q in cands)
            if g["active"] and v_scan != g["V"]:
                bad_val.append((k, str(t), str(rho), str(v_scan - g["V"])))
            # (b) two-action dominance: every d is >= the corresponding mixture
            for h in range(1, k + 1):
                for d in range(0, k + 1):
                    mix = (1 - F(d, k)) * risk0(s["e"], s["r"], F(h)) + \
                          F(d, k) * base(k, s["p"], s["cden"], s["e"], s["r"], F(h), F(k))
                    if d == 0:
                        act = risk0(s["e"], s["r"], F(h))
                    elif d == 1:
                        act = riskOne(k, s["p"], s["cden"], s["e"], s["r"], s["b"], F(h))
                    else:
                        act = riskGen(k, s["p"], s["cden"], s["e"], s["r"], F(h), F(d))
                    if mix > act:
                        bad_dom.append((k, str(t), str(rho), h, d, str(mix - act)))
n_active = sum(1 for k in CHECK_K for t in CHECK_T for rho in CHECK_R
               if game(k, t, rho)["active"])
print(f"cells scanned: {n_cells}, in the sufficient regime (k-2)b>=1: {n_suff}, "
      f"ACTIVE (k*r>e, so V>0 and the check is not vacuous): {n_active}")
print("2x2 minimax != phaseValueFull (exact):", bad_val if bad_val else "none")
print("two-action dominance violations (exact):", bad_dom[:5] if bad_dom else "none",
      f"({len(bad_dom)} total)" if bad_dom else "")
print("NOTE: dominance_one in Lean assumes b <= e; e = min(a,2b) so b<=e always holds here.")

# ------------------------------------------ 1. is the regret linear or quadratic?
print()
print("=" * 78)
print("1. TRUE plug-in decision regret vs |err|.  Exponent = log-ratio between")
print("   successive decades.  1.0 = LINEAR, 2.0 = QUADRATIC.")
print("=" * 78)
print(f"{'k':>5} {'t':>8} {'rho':>6} {'suff':>5} {'|err|':>9} {'TRUE regret':>14} "
      f"{'reg/|err|':>12} {'reg/err^2':>12} {'exponent':>9}")
rows = []
# ACTIVE-regime grid.  The reference must scale as t = tau/k (the growing-
# dimension regime of the derivation note), otherwise a -> 0, r = 2a-rho < 0
# and the game is inactive with V == 0 -- which makes every regret trivially
# zero and the whole probe vacuous.  This grid was CHOSEN to be active; the
# `active` column below is the check that it really is.
CASES = []
for k in (8, 32, 128):
    for tau_num, tau_den in ((1, 20), (1, 10), (3, 20), (1, 5)):
        t = F(tau_num, tau_den * k)
        for rho in (F(1), F(5, 4), F(3, 2)):
            if game(k, t, rho)["active"]:
                CASES.append((k, t, rho))
CASES = CASES[:8] + CASES[-4:]
print(f"\nactive cases used below: {len(CASES)} "
      f"(a grid of 36 (k,tau,rho) cells was screened; only active ones kept)")
for (k, t, rho) in CASES:
    g0 = game(k, t, rho)
    suff = (k - 2) * g0["s"]["b"] >= 1
    prev = None
    for m in range(1, 7):
        err = t / 10 ** m          # RELATIVE decades: t itself is O(1/k) here
        for sgn in (1, -1):
            that = t + sgn * err
            if that <= 0 or that > F(1, 2):
                continue
            reg, gt, gh = true_regret(k, t, rho, that)
            expo = ""
            if sgn == 1:
                if prev is not None and reg > 0:
                    import math
                    expo = f"{math.log(float(prev) / float(reg)) / math.log(10):.3f}"
                prev = reg
            print(f"{k:>5} {str(t):>8} {str(rho):>6} {str(suff):>5} "
                  f"{('+' if sgn>0 else '-')+'t/1e'+str(m):>9} {float(reg):>14.6e} "
                  f"{float(reg)/float(err):>12.6e} {float(reg)/float(err)**2:>12.6e} {expo:>9}")
            rows.append(dict(k=k, t=str(t), rho=str(rho), sufficient=bool(suff),
                             err=float(sgn * err), regret=float(reg),
                             reg_over_abserr=float(reg) / float(err),
                             reg_over_err2=float(reg) / float(err) ** 2))
results = {"linearity": rows}

# ------------------------------- 2. current-style bound vs proposed kink bound
print()
print("=" * 78)
print("2. CURRENT-STYLE bound (2 * uniform value-Lipschitz modulus * |err|)")
print("   vs PROPOSED direct decision-regret bound.")
print("=" * 78)
print("  L_V   := sup over the err-interval of |dV/dt|, by exact difference quotient")
print("  current  = 2 * L_V * |err|        (the estimated_optimizer_regret shape)")
print("  proposed = Sm * (qq*(t) - qq*(that))_+  +  U * (qq*(that) - qq*(t))_+ ,")
print("             Sm = v - u0 >= 0 and U >= 0 are the two one-sided slopes of")
print("             max_h risk in the DECISION variable qq.  Units: value per unit qq.")
print()
print(f"{'k':>5} {'t':>8} {'rho':>6} {'|err|':>8} {'TRUE':>13} {'current':>13} "
      f"{'proposed':>13} {'T/cur':>11} {'T/prop':>9}")
rows2 = []
for (k, t, rho) in CASES:
    for m in (2, 4):
        err = t / 10 ** m
        for sgn in (1, -1):
            that = t + sgn * err
            if that <= 0 or that > F(1, 2):
                continue
            reg, gt, gh = true_regret(k, t, rho, that)
            LV = abs(game(k, that, rho)["V"] - gt["V"]) / err
            cur = 2 * LV * err
            Sm = gt["v"] - gt["u0"]
            dq = gh["qstar"] - gt["qstar"]
            prop = Sm * (-dq if dq < 0 else F(0)) + gt["U"] * (dq if dq > 0 else F(0))
            print(f"{k:>5} {str(t):>8} {str(rho):>6} {('+' if sgn>0 else '-')+'t/1e'+str(m):>8} "
                  f"{float(reg):>13.5e} {float(cur):>13.5e} {float(prop):>13.5e} "
                  f"{(float(reg)/float(cur) if cur else float('nan')):>11.3e} "
                  f"{(float(reg)/float(prop) if prop else float('nan')):>9.5f}")
            rows2.append(dict(k=k, t=str(t), rho=str(rho), err=float(sgn * err),
                              true=float(reg), current=float(cur), proposed=float(prop),
                              ratio_true_current=(float(reg) / float(cur) if cur else None),
                              ratio_true_proposed=(float(reg) / float(prop) if prop else None)))
results["bounds"] = rows2

# ------------------------------------------ 3. the kink law at the phase boundary
print()
print("=" * 78)
print("3. THE KINK LAW.  rho_crit = 2a - e/k is where k*r = e and the value")
print("   collapses (phaseValueFull_zero).  The two one-sided DECISION slopes")
print("   (v-u0) and U are wildly asymmetric there: over-shooting d=0 is free,")
print("   under-shooting is not.  Units: value per unit of decision weight qq.")
print("=" * 78)
print(f"{'k':>5} {'t':>8} {'rho':>14} {'rho/rho_crit':>13} {'V':>12} {'qq*':>10} "
      f"{'Sm=v-u0':>11} {'U':>11} {'U/Sm':>11}")
rows3 = []
# t = tau/k with tau = 1/10 keeps rho_crit = 2a - e/k inside the modelled
# range 1 <= rho <= 2.  (At tau = 1, rho_crit < 1 and no admissible rho reaches
# the boundary at all -- that grid would have been vacuous.)
for k in (8, 32, 128):
    t = F(1, 10 * k)
    rc = rho_crit(k, t)
    print(f"   [k={k}, t=1/{10*k}: rho_crit = {float(rc):.8f}, "
          f"admissible = {bool(1 <= rc <= 2)}]")
    for mult in (F(3, 5), F(4, 5), F(9, 10), F(99, 100), F(1), F(101, 100)):
        rho = rc * mult
        if rho < 1 or rho > 2:
            continue
        g = game(k, t, rho)
        Sm = g["v"] - g["u0"]
        print(f"{k:>5} {str(t):>8} {float(rho):>14.8f} {float(mult):>13.4f} "
              f"{float(g['V']):>12.5e} {float(g['qstar']):>10.6f} {float(Sm):>11.5e} "
              f"{float(g['U']):>11.4e} "
              f"{(float(g['U'])/float(Sm) if Sm else float('nan')):>11.4e}")
        rows3.append(dict(k=k, t=str(t), rho=float(rho), rho_over_crit=float(mult),
                          V=float(g["V"]), qstar=float(g["qstar"]),
                          slope_minus=float(Sm), slope_plus=float(g["U"]),
                          asymmetry=(float(g["U"]) / float(Sm) if Sm else None)))
results["kink"] = rows3
print()
print()
print("one-sided regret exactly AT rho = rho_crit (k=32, t=1/320, so rho_crit is")
print("admissible).  err is relative: that = t*(1 +/- 10^-m).")
k, t = 32, F(1, 320)
rc = rho_crit(k, t)
print(f"   rho_crit = {float(rc)!r}  admissible(1<=rho<=2): {bool(1 <= rc <= 2)}")
for sgn in (1, -1):
    for m in (3, 4, 5):
        err = t / 10 ** m
        reg, gt, gh = true_regret(k, t, rc, t + sgn * err)
        print(f"   err={'+' if sgn>0 else '-'}t/1e{m}:  regret = {float(reg):.6e}   "
              f"regret/|err| = {float(reg)/float(err):.6e}")
        results.setdefault("boundary_onesided", []).append(
            dict(k=k, t=str(t), rho=float(rc), err=float(sgn * err),
                 regret=float(reg), reg_over_abserr=float(reg) / float(err)))

out = "/Users/phanan/cig-amf-main/scripts/A07_reference_phase_regret.json"
with open(out, "w") as f:
    json.dump(results, f, indent=1)
print("\nwrote", out)
