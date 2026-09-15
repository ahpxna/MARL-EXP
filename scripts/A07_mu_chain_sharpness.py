#!/usr/bin/env python3
"""
A07 probe 1: how loose is the adaptive local value bound in the mu-chain?

All formulas are transcribed from the Lean sources (paths in TRANSCRIBED_FROM
below).  Nothing here is a model or an approximation of the Lean definitions --
each python function is a literal transcription of one `def`.

Units / variables, stated explicitly because the supervisor asked:

  mu      : the TRUE MARGIN, the statistical parameter.  Dimensionless, in [0,1].
            Everything called `*Modulus` or `*Constant` below is a coefficient
            in an expansion in POWERS OF (mu - mu0), i.e. per unit of margin.
  w       : the ALLOCATION WEIGHT (`mass q mu0`), dimensionless, in [0,1/4] on
            the phase-III interval.  `coefficient q w` is curvature of the loss
            in the NUISANCE coordinate u, NOT in mu.  `localCurvature q mu0`
            (LeanD6LocalMatchingDesignV1) is also a weight-space object.
            These are DIFFERENT variables from mu and are never mixed here.
  u       : the nuisance coordinate of the alternative world.  `coefficient q w`
            has units of (loss)/(u^2); `(shift - delta)` has units of u;
            so `coefficient*(shift-delta)^2/2` has units of loss.  Good.

TRANSCRIBED_FROM (all under work/p13_conjectures/):
  LeanD6ExpandedAllocationV1.lean          scale, value, root
  LeanD6AllocationMarginRegionV1.lean      tilt, radius, marginMin, marginMax
  LeanD6AllocationMarginV1.lean            rate (phase II)
  LeanD6AllocationPhaseThreeFeasibleV1.lean marginHigh
  LeanD6AllocationPhaseThreeParametersV1.lean K, radicand, D, shift, mass
  LeanD6AllocationPhaseThreeCoreV1.lean    coefficient, gammaTwice
  LeanD6FrozenScalarAllocationV1.lean      p, beta, delta, value
  LeanD6PhaseThreeSharpV1.lean             rate (phase III)
  LeanD6PhaseShiftLipschitzV1.lean         radicalModulus, shiftModulus
  LeanD6FrozenQuadraticBoundV1.lean        combinedModulus, remainderConstant
  LeanD6OracleValueStabilityV1.lean        marginModulus
  LeanD6AllocationTrackingStabilityV1.lean informationCap
  LeanD6CyclicConfidenceSequenceV1.lean    varianceParameter, epochError, width
  LeanD6LocalMatchingDesignV1.lean         leftCoefficient, localCurvature
  LeanD6LocalMatchingAlgebraV1.lean        curvatureDifference

Run:  python3 scripts/A07_mu_chain_sharpness.py
"""
import json
import sys
from mpmath import mp, mpf, sqrt, log, diff, findroot

mp.dps = 60

# ---------------------------------------------------------------- definitions

def scale(q):            return sqrt(q / (q + 1))
def val_expanded(q, c):  return (c * (q - 1) / (q - 2 + c)) ** 2
def root(q, c):          return (1 - c) / (q - 2 + c)
def tilt(q):             return root(q, scale(q))
def radius(q):
    t = tilt(q)
    return sqrt((q**2 + 2 * q**2 * t + t**2) / (q + 1))
def marginMin(q):        return (1 - scale(q)) / (q - 1)
def marginMax(q):        return radius(q) / (1 + radius(q))
def marginHigh(q):       return sqrt(q) / (1 + sqrt(q))

def K(q):                return q * (q - 2) ** 2 - q + 1
def radicand(q, mu):     return q * (q - 1) * (1 - mu) ** 2 + K(q) * mu**2
def D(q, mu):            return sqrt(radicand(q, mu))
def shift(q, mu):        return (q * (1 - mu) ** 2 - mu**2) / (q * (q - 2) * (1 - mu) + D(q, mu))
def mass(q, mu):         return (q - 1) * shift(q, mu) / D(q, mu)

def coefficient(q, w):   return (1 - w) * (q - 1) / q + w * (q - 2) ** 2
def delta(q, w, mu):     return w * (q - 2) * (1 - mu) / coefficient(q, w)
def gammaTwice(q, mu, s): return (mu**2 + (q - 1) * s**2) / q

def rate3(q, mu):        return gammaTwice(q, mu, shift(q, mu)) / 2       # phase-III oracle value
def rate2(q, lam):       return lam**2 * val_expanded(q, scale(q)) / 2    # phase-II  oracle value

def p_frozen(q, w):      return (1 - w) / q
def beta_frozen(q, w):   return (1 - w) * (q - 1) * w / (q * coefficient(q, w))
def leftCoefficient(q):  return val_expanded(q, scale(q))
def localCurvature(q, mu0):
    w = mass(q, mu0)
    return (p_frozen(q, w) + beta_frozen(q, w) - leftCoefficient(q)) / 2

def radicalModulus(q, mu0): return 2 * (q * (q - 1) + K(q)) / D(q, mu0)
def shiftModulus(q, mu0):   return (q * (q - 2) + radicalModulus(q, mu0)) / K(q)
def combinedModulus(q, mu0):
    w = mass(q, mu0)
    return shiftModulus(q, mu0) + abs(w * (q - 2) / coefficient(q, w))
def remainderConstant(q, mu0):
    return coefficient(q, mass(q, mu0)) * combinedModulus(q, mu0) ** 2 / 2

def marginModulus(q):    return 2 * q * (2 * q + 1)
def informationCap(q):   return (q + 2) ** 2 / 2

def width(q, L0, s, dl, card=None):
    """LeanD6CyclicConfidenceSequenceV1.width_formula, card C = 2q+1 for D6."""
    if card is None:
        card = 2 * q + 1
    L = L0 * 2**s
    ee = dl / ((s + 1) * (s + 2))
    return sqrt(2 * (card / (L * q**4)) * log(2 / ee))

# ------------------------------------------------- the EXACT frozen-gap regret
# LeanD6FrozenOracleGapV1.actual_frozen_oracle_gap is an EQUALITY:
#   oracleRegret A j q mu (queries A j) (weights A j q w)
#     = coefficient q w * (shift q mu - delta q w mu)^2 / 2
# with w = mass q mu0 (design frozen at the estimate mu0).

def exact_frozen_regret(q, mu0, mu):
    w = coefficient(q, mass(q, mu0))
    g = shift(q, mu) - delta(q, mass(q, mu0), mu)
    return w * g**2 / 2

def gprime(q, mu0, mu):
    """d/dmu [ shift(q,.) - delta(q, mass(q,mu0), .) ]  -- units: u per unit mu."""
    w = mass(q, mu0)
    return diff(lambda m: shift(q, m), mu) + w * (q - 2) / coefficient(q, w)

# -------------------------------------------------------------------- reports

def section(t):
    print()
    print("=" * 78)
    print(t)
    print("=" * 78)

results = {}

QS = [mpf(8), mpf(16), mpf(32), mpf(64), mpf(128), mpf(256), mpf(1024)]

# ---- 1. phase geometry + is the oracle value continuous across the boundary?
section("1. phase geometry, and the phase-II / phase-III junction")
print(f"{'q':>6} {'marginMin':>12} {'marginMax':>12} {'marginHigh':>12} "
      f"{'rate2@Max':>14} {'rate3@Max':>14} {'rel.jump':>11}")
geom = []
for q in QS:
    mM, mX, mH = marginMin(q), marginMax(q), marginHigh(q)
    r2 = rate2(q, 1 - mX)
    r3 = rate3(q, mX)
    rel = abs(r2 - r3) / max(abs(r2), abs(r3))
    print(f"{int(q):>6} {mp.nstr(mM,6):>12} {mp.nstr(mX,6):>12} {mp.nstr(mH,6):>12} "
          f"{mp.nstr(r2,6):>14} {mp.nstr(r3,6):>14} {mp.nstr(rel,3):>11}")
    geom.append(dict(q=int(q), marginMin=float(mM), marginMax=float(mX),
                     marginHigh=float(mH), rate2_at_marginMax=float(r2),
                     rate3_at_marginMax=float(r3), rel_jump=float(rel)))
results["phase_geometry"] = geom

# ---- 2. how loose is marginModulus as a Lipschitz modulus of the ORACLE VALUE?
section("2. marginModulus(q)=2q(2q+1) vs the TRUE |d(oracleValue)/dmu| "
        "on the two intervals where a closed form is PROVED")
print(f"{'q':>6} {'marginModulus':>14} {'supP2|dV/dmu|':>15} {'supP3|dV/dmu|':>15} "
      f"{'loose x (P3)':>14} {'loose x (P2)':>14}")
loose = []
for q in QS:
    mM, mX, mH = marginMin(q), marginMax(q), marginHigh(q)
    # phase II: mu in [marginMin, marginMax], oracleValue = rate2(q, 1-mu)
    g2 = max(abs(diff(lambda m: rate2(q, 1 - m), mM + (mX - mM) * mpf(i) / 40))
             for i in range(41))
    # phase III: mu in [marginMax, marginHigh], oracleValue = rate3(q, mu)
    g3 = max(abs(diff(lambda m: rate3(q, m), mX + (mH - mX) * mpf(i) / 40))
             for i in range(41))
    mm = marginModulus(q)
    print(f"{int(q):>6} {mp.nstr(mm,6):>14} {mp.nstr(g2,6):>15} {mp.nstr(g3,6):>15} "
          f"{mp.nstr(mm/g3,4):>14} {mp.nstr(mm/g2,4):>14}")
    loose.append(dict(q=int(q), marginModulus=float(mm), supII=float(g2),
                      supIII=float(g3), looseness_III=float(mm / g3),
                      looseness_II=float(mm / g2)))
results["lipschitz_looseness"] = loose

# ---- 3. the quadratic coefficient: certified vs sharp (cancellation test)
section("3. quadratic route.  combinedModulus is |shift'|+|delta'| (triangle "
        "ineq).  The sharp constant is |shift'-delta'|.  Do they cancel?")
print(f"{'q':>6} {'mu0':>10} {'q*shift\'':>12} {'q*delta\'':>12} {'q*|g\'|':>12} "
      f"{'q*combMod':>12} {'cancel x':>10}")
cancel = []
for q in QS:
    mX, mH = marginMax(q), marginHigh(q)
    for frac in (mpf("0.05"), mpf("0.25"), mpf("0.5"), mpf("0.75"), mpf("0.95")):
        mu0 = mX + (mH - mX) * frac
        w = mass(q, mu0)
        sp = diff(lambda m: shift(q, m), mu0)
        dp = -w * (q - 2) / coefficient(q, w)
        gp = sp - dp
        cm = combinedModulus(q, mu0)
        print(f"{int(q):>6} {mp.nstr(mu0,5):>10} {mp.nstr(q*sp,5):>12} "
              f"{mp.nstr(q*dp,5):>12} {mp.nstr(q*abs(gp),5):>12} "
              f"{mp.nstr(q*cm,5):>12} {mp.nstr(cm/abs(gp),4):>10}")
        cancel.append(dict(q=int(q), frac=float(frac), mu0=float(mu0),
                           q_shiftprime=float(q * sp), q_deltaprime=float(q * dp),
                           q_absgprime=float(q * abs(gp)),
                           q_combinedModulus=float(q * cm),
                           cancellation_factor=float(cm / abs(gp))))
results["cancellation"] = cancel

# ---- 4. remainderConstant: certified 64/q^2 vs actual vs sharp
section("4. remainderConstant(q,mu0) vs the certified 64/q^2 vs the sharp "
        "coefficient (coefficient/2)*sup g'^2")
print(f"{'q':>6} {'mu0':>10} {'64/q^2':>13} {'remainderC':>13} {'sharpC':>13} "
      f"{'64/q^2 / sharp':>15}")
rc = []
for q in QS:
    mX, mH = marginMax(q), marginHigh(q)
    for frac in (mpf("0.05"), mpf("0.5"), mpf("0.95")):
        mu0 = mX + (mH - mX) * frac
        cw = coefficient(q, mass(q, mu0))
        # sup over the whole phase interval (worst case, conservative)
        sup_gp = max(abs(gprime(q, mu0, mX + (mH - mX) * mpf(i) / 40)) for i in range(41))
        sharp = cw * sup_gp**2 / 2
        cert = 64 / q**2
        r = remainderConstant(q, mu0)
        print(f"{int(q):>6} {mp.nstr(mu0,5):>10} {mp.nstr(cert,5):>13} "
              f"{mp.nstr(r,5):>13} {mp.nstr(sharp,5):>13} {mp.nstr(cert/sharp,5):>15}")
        rc.append(dict(q=int(q), mu0=float(mu0), cert_64_over_q2=float(cert),
                       remainderConstant=float(r), sharp_global=float(sharp),
                       ratio_cert_over_sharp=float(cert / sharp)))
results["remainder_constants"] = rc

# ---- 5. TRUE regret vs current bound vs proposed bound, on a grid
section("5. TRUE frozen-design regret vs the CURRENT chain bound "
        "(2*marginModulus*eps) vs the PROPOSED bound")
print("current  = 2*marginModulus(q)*eps                     [Lipschitz, phase-agnostic]")
print("certQuad = (64/q^2)*eps^2                             [remainder_scaled, PROVED]")
print("proposed = (coefficient(q,mass(q,mu0))/2)*Mloc^2*eps^2, Mloc = sup|g'| on [mu0-eps,mu0+eps]")
print()
print(f"{'q':>5} {'mu0frac':>8} {'eps':>10} {'TRUE':>12} {'current':>12} "
      f"{'certQuad':>12} {'proposed':>12} {'T/cur':>10} {'T/cert':>9} {'T/prop':>9}")
grid = []
for q in QS:
    mX, mH = marginMax(q), marginHigh(q)
    for frac in (mpf("0.25"), mpf("0.75")):
        mu0 = mX + (mH - mX) * frac
        for e in ("1e-1", "1e-2", "1e-3", "1e-5"):
            eps = mpf(e)
            for sgn in (1, -1):
                mu = mu0 + sgn * eps
                if mu < mX or mu > mH:
                    continue
                true = exact_frozen_regret(q, mu0, mu)
                cur = 2 * marginModulus(q) * eps
                cert = (64 / q**2) * eps**2
                lo, hi = max(mX, mu0 - eps), min(mH, mu0 + eps)
                Mloc = max(abs(gprime(q, mu0, lo + (hi - lo) * mpf(i) / 20)) for i in range(21))
                prop = coefficient(q, mass(q, mu0)) * Mloc**2 * eps**2 / 2
                print(f"{int(q):>5} {mp.nstr(frac,3):>8} {('+' if sgn>0 else '-')+e:>10} "
                      f"{mp.nstr(true,5):>12} {mp.nstr(cur,5):>12} {mp.nstr(cert,5):>12} "
                      f"{mp.nstr(prop,5):>12} {mp.nstr(true/cur,4):>10} "
                      f"{mp.nstr(true/cert,4):>9} {mp.nstr(true/prop,4):>9}")
                grid.append(dict(q=int(q), frac=float(frac), eps=float(sgn * eps),
                                 true=float(true), current=float(cur),
                                 certQuad=float(cert), proposed=float(prop),
                                 ratio_true_over_current=float(true / cur),
                                 ratio_true_over_cert=float(true / cert),
                                 ratio_true_over_proposed=float(true / prop)))
results["regret_grid"] = grid

# ---- 6. what L does each route need for an absolute target eta = q^-2 ?
section("6. epoch length L needed for an ABSOLUTE regret target eta = q^-2")
print("route A (current, high probability, delta=0.05, s=0):  2*marginModulus*width(L) <= eta")
print("route B (proposed, in EXPECTATION, no log):            (64/q^2)*E[(mhat-mu)^2] <= eta,")
print("                                                       E[(mhat-mu)^2] <= (2q+1)/(L q^4)")
print("route C (proposed, high probability, delta=0.05,s=0):  (64/q^2)*width(L)^2 <= eta")
print()
print(f"{'q':>6} {'eta=q^-2':>12} {'L_A':>14} {'L_B':>12} {'L_C':>12} "
      f"{'rawA=L_A(2q+1)':>16} {'rawB':>12}")
need = []
dl = mpf("0.05")
for q in QS:
    eta = 1 / q**2
    # route A: width(L) <= eta/(2*marginModulus) ; width^2 = 2*(2q+1)/(L q^4)*log(2/delta)
    wA = eta / (2 * marginModulus(q))
    LA = 2 * (2 * q + 1) * log(2 / dl) / (q**4 * wA**2)
    # route B
    LB = (64 / q**2) * (2 * q + 1) / (q**4 * eta)
    # route C
    wC2 = eta / (64 / q**2)
    LC = 2 * (2 * q + 1) * log(2 / dl) / (q**4 * wC2)
    print(f"{int(q):>6} {mp.nstr(eta,5):>12} {mp.nstr(LA,6):>14} {mp.nstr(LB,5):>12} "
          f"{mp.nstr(LC,5):>12} {mp.nstr(LA*(2*q+1),6):>16} {mp.nstr(LB*(2*q+1),5):>12}")
    need.append(dict(q=int(q), eta=float(eta), L_current=float(LA), L_meansquare=float(LB),
                     L_highprob_quadratic=float(LC),
                     raw_current=float(LA * (2 * q + 1)), raw_meansquare=float(LB * (2 * q + 1))))
results["sample_size"] = need

# fit exponents in q for L_A and L_C
import math
def fit_exponent(xs, ys):
    lx = [math.log(x) for x in xs]
    ly = [math.log(y) for y in ys]
    n = len(lx)
    mx, my = sum(lx) / n, sum(ly) / n
    return sum((a - mx) * (b - my) for a, b in zip(lx, ly)) / sum((a - mx) ** 2 for a in lx)

qs = [d["q"] for d in need]
print()
print("fitted exponent  L ~ q^alpha  (log-log slope over q=8..1024):")
print(f"  route A (current)        alpha = {fit_exponent(qs,[d['L_current'] for d in need]):.4f}")
print(f"  route B (mean square)    alpha = {fit_exponent(qs,[d['L_meansquare'] for d in need]):.4f}")
print(f"  route C (hp quadratic)   alpha = {fit_exponent(qs,[d['L_highprob_quadratic'] for d in need]):.4f}")
results["fitted_exponents"] = dict(
    L_current=fit_exponent(qs, [d["L_current"] for d in need]),
    L_meansquare=fit_exponent(qs, [d["L_meansquare"] for d in need]),
    L_highprob_quadratic=fit_exponent(qs, [d["L_highprob_quadratic"] for d in need]))

# ---- 7. residual / self-check: exact identity holds, and clip never hurts
section("7. self-checks")
maxres = mpf(0)
for q in QS:
    mX, mH = marginMax(q), marginHigh(q)
    mu0 = mX + (mH - mX) / 3
    # frozen_shift_at_design:  delta(q, mass(q,mu0), mu0) == shift(q,mu0)
    res = abs(delta(q, mass(q, mu0), mu0) - shift(q, mu0))
    maxres = max(maxres, res)
    # regret at mu == mu0 must be exactly 0
    maxres = max(maxres, abs(exact_frozen_regret(q, mu0, mu0)))
print("max |delta(q,mass(q,mu0),mu0) - shift(q,mu0)| and |regret(mu0;mu0)| over the grid:",
      mp.nstr(maxres, 5), " (mp.dps =", mp.dps, ")")
results["selfcheck_residual"] = float(maxres)
# phase_mass_bounds sanity: 0 <= mass <= 1/4
bad = []
for q in QS:
    mX, mH = marginMax(q), marginHigh(q)
    for i in range(41):
        mu = mX + (mH - mX) * mpf(i) / 40
        w = mass(q, mu)
        if w < 0 or w > mpf(1) / 4:
            bad.append((int(q), float(mu), float(w)))
print("phase_mass_bounds violations (0<=mass<=1/4):", bad if bad else "none")
results["mass_bound_violations"] = bad

out = "/Users/phanan/cig-amf-main/scripts/A07_mu_chain_sharpness.json"
with open(out, "w") as f:
    json.dump(results, f, indent=1)
print("\nwrote", out)
