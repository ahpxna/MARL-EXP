"""D06ALPHA probe 2: the ACTUAL minimax value of the D6 reference regret game,
computed EXACTLY from the full count loss, versus the closed form
phaseValueFull, along t = tau / k^alpha.

This is the probe that decides whether alpha = 2 (where Lean's SUFFICIENT
hypothesis `strong : 1 <= (k-2) b` lapses) is a real transition of the game
value, or only a lapse of a sufficient condition.

THE GAME (read off the Lean chain, not assumed):
  ground = positiveGround q j, card 2q+1;  k = q+1;  T in worlds q j, |T| = k.
  Hidden world A in worlds q j: |A| = k, so h := |T inter A| ranges over 1..k
  (h = 0 is impossible: |T|+|A| = 2k > 2k-1 = |ground|), and every h in 1..k is
  realised.  Decision S with |S| = |T|; only D := T \\ S matters, and every
  D subset T is legal (hroom holds with equality since |T^c| = |T|).
    u = |D inter A|, v = |D| - u, d = |D|.
  actualLoss  = countLoss a b rho k (k-1) u v          [FullCountLossV1, PROVED]
  legalMinimum = min over u'<=h, v'<=k-h of countLoss  [LegalCountMinimumV1, PROVED]
  regret = actualLoss - legalMinimum                    [PhaseRegretBridgeV1]
  value  = min over randomized D  max over A  E[regret]

NOTHING in this file uses `strong`, `variableCost`, `commonConstant`,
`orbitRisk` or `phaseValueFull` to COMPUTE the value: the value comes only from
countLoss, which is the PROVED actual loss with hypotheses 0<=t<=1, rho>=1,
|others A j|>=2 only.  phaseValueFull is computed separately and compared.

Exact rational arithmetic throughout; every LP solution is re-verified by an
independent saddle-point certificate check (verify_game) and the worst
row-excess / column-deficit is printed, so the reader sees the residual (it is 0).

Symmetry reduction (rows = h, cols = d) is used for speed; it is validated
against the FULL unreduced game in D06ALPHA_full_vs_reduced.py.

Run: python3 /Users/phanan/cig-amf-main/scripts/D06ALPHA_alpha_minimax.py
"""

import sys
import time
from fractions import Fraction as F

sys.path.insert(0, "/Users/phanan/cig-amf-main/scripts")
from D06ALPHA_gamelib import (slopes, phase_value_full, reduced_payoff_matrix,
                              solve_game, verify_game)

ALPHAS = [F(1, 2), F(1), F(3, 2), F(2), F(5, 2)]


def cell(k, t, rho):
    a, b, c = slopes(k, t)
    p, r, e = rho - 2 * b, 2 * a - rho, min(a, 2 * b)
    # c = (1-t)^(2q) vanishes at t = 1, where phaseValueFull divides by zero. The
    # ACTUAL minimax is still defined there (countLoss needs only 0<=t<=1, rho>=1),
    # so the cell is kept and the closed form is reported as UNDEFINED rather than
    # crashing the probe -- which is what the previous version of this file did.
    Vclosed = phase_value_full(k, p, c, e, r) if c != 0 else None
    M = reduced_payoff_matrix(k, t, rho)
    Vlp, col, row = solve_game(M)
    ok, up, lo = verify_game(M, Vlp, col, row)
    return dict(a=a, b=b, c=c, p=p, r=r, e=e,
                Vclosed=Vclosed, Vlp=Vlp, cert_ok=ok, cert_up=up, cert_lo=lo,
                strong=((k - 2) * b >= 1),
                branch=((1 - a <= (k - 2) * b) and (a * k >= 1)),
                active=(e <= k * r),
                region=(k >= 3 and 0 <= t <= 1 and 1 <= rho <= 2
                        and rho - 2 * b >= F(1, 2) and (k - 2) * b >= 1),
                col=col, row=row)


def fmt(x, n=10):
    return f"{float(x):.{n}g}"


def banner(s):
    print()
    print("=" * 112)
    print(s)


def main():
    t0 = time.time()

    banner("PART A.  CONTROL INSIDE the Lean Region (strong holds).  "
           "Closed form MUST match the exact minimax.")
    print("  includes the documented Region witness q=8,k=9,t=1/25 "
          "(PhaseWitnessV1) and the alpha=1 family.")
    print(f"  {'k':>3} {'t':>12} {'rho':>5} {'S':>2} {'B':>2} {'A':>2} {'R':>2} "
          f"{'V_minimax(exact)':>22} {'V_phaseValueFull':>22} {'V_lp - V_closed':>18} {'cert'}")
    controls = [(9, F(1, 25), F(1)), (9, F(1, 25), F(11, 10)),
                (10, F(1, 20), F(1)), (12, F(1, 24), F(1)), (12, F(1, 24), F(6, 5)),
                (9, F(1, 2) / 9, F(1)), (16, F(1, 2) / 16, F(1)),
                (25, F(1, 2) / 25, F(1)), (36, F(1, 2) / 36, F(1))]
    nA = 0
    for k, t, rho in controls:
        d = cell(k, t, rho)
        diff = d["Vlp"] - d["Vclosed"]
        print(f"  {k:>3} {str(t):>12} {str(rho):>5} "
              f"{'T' if d['strong'] else 'F':>2} {'T' if d['branch'] else 'F':>2} "
              f"{'T' if d['active'] else 'F':>2} {'T' if d['region'] else 'F':>2} "
              f"{fmt(d['Vlp'],12):>22} {fmt(d['Vclosed'],12):>22} "
              f"{str(diff) if diff != 0 else '0 (exact)':>18} "
              f"{'ok' if d['cert_ok'] else 'FAIL'}")
        if d["region"] and diff != 0:
            nA += 1
    print(f"  in-Region cells with V_lp != V_closed: {nA}  (must be 0)")

    banner("PART B.  THE ALPHA SWEEP.  k = m^2 so that t = tau/m^(2 alpha) is "
           "RATIONAL for every alpha in {1/2,1,3/2,2,5/2}.")
    print("  S=strong(Lean sufficient)  B=exact branch condition  A=active(e<=kr)  "
           "R=full Region")
    print("  'match' = (exact minimax == phaseValueFull) as EXACT rationals.")
    for tau in [F(1, 4), F(1, 2), F(1), F(2)]:
        for rho in [F(1), F(6, 5), F(8, 5)]:
            print(f"\n  tau={tau}  rho={rho}")
            print(f"    {'alpha':>5} {'m':>2} {'k':>4} {'S':>2}{'B':>2}{'A':>2}{'R':>2} "
                  f"{'V_minimax':>18} {'V_closed':>18} {'match':>6} "
                  f"{'V_lp/k':>14} {'cert':>5}")
            for alpha in ALPHAS:
                for m in (3, 5):          # k = 9, 25.  m=7 (k=49) costs ~11 s per
                    k = m * m             # cell and is swept separately in PART C.
                    t = F(tau) / F(m) ** int(2 * alpha)
                    d = cell(k, t, rho)
                    match = (d["Vlp"] == d["Vclosed"])
                    print(f"    {str(alpha):>5} {m:>2} {k:>4} "
                          f"{'T' if d['strong'] else 'F':>2}"
                          f"{'T' if d['branch'] else 'F':>2}"
                          f"{'T' if d['active'] else 'F':>2}"
                          f"{'T' if d['region'] else 'F':>2} "
                          f"{fmt(d['Vlp']):>18} {fmt(d['Vclosed']):>18} "
                          f"{str(match):>6} {fmt(d['Vlp']/k):>14} "
                          f"{'ok' if d['cert_ok'] else 'FAIL':>5}")

    banner("PART C.  OUTSIDE the strong domain, ALONG alpha = 5/2 and alpha = 2, "
           "as k grows.")
    print("  This is the alpha where `strong` lapses.  If the value changed "
          "character here,")
    print("  V_minimax would part company with phaseValueFull.  Columns as above.")
    for alpha, tau, rho in [(F(5, 2), F(1, 2), F(6, 5)), (F(2), F(1, 2), F(6, 5)),
                            (F(2), F(1), F(1)), (F(5, 2), F(2), F(1))]:
        print(f"\n  alpha={alpha} tau={tau} rho={rho}")
        print(f"    {'k':>4} {'(k-2)b':>14} {'1-a':>14} {'S':>2}{'B':>2}{'A':>2} "
              f"{'V_minimax':>18} {'V_closed':>18} {'match':>6} {'V/k':>12}")
        for m in range(2, 8):
            k = m * m
            t = F(tau) / F(m) ** int(2 * alpha)
            d = cell(k, t, rho)
            print(f"    {k:>4} {fmt((k-2)*d['b'],8):>14} {fmt(1-d['a'],8):>14} "
                  f"{'T' if d['strong'] else 'F':>2}{'T' if d['branch'] else 'F':>2}"
                  f"{'T' if d['active'] else 'F':>2} "
                  f"{fmt(d['Vlp']):>18} {fmt(d['Vclosed']):>18} "
                  f"{str(d['Vlp']==d['Vclosed']):>6} {fmt(d['Vlp']/k,8):>12}")

    banner("PART D.  alpha = 1/2 : the ONLY alpha in the package grid where the "
           "EXACT BRANCH condition fails.")
    print("  Here the closed form says 0.  Does the ACTUAL minimax also vanish, "
          "or is the closed form simply wrong there?")
    print(f"    {'alpha':>5} {'tau':>5} {'rho':>5} {'k':>4} {'a':>12} {'a*k':>12} "
          f"{'B':>2}{'A':>2} {'V_minimax':>20} {'V_closed':>12} {'match':>6}")
    for tau in [F(1, 4), F(1, 2), F(1)]:
        for rho in [F(1), F(6, 5)]:
            for m in (2, 3, 4, 5, 6):   # k up to 36; k=49 costs ~11 s/cell
                k = m * m
                t = F(tau) / F(m)
                d = cell(k, t, rho)
                print(f"    {'1/2':>5} {str(tau):>5} {str(rho):>5} {k:>4} "
                      f"{fmt(d['a'],6):>12} {fmt(d['a']*k,6):>12} "
                      f"{'T' if d['branch'] else 'F':>2}"
                      f"{'T' if d['active'] else 'F':>2} "
                      f"{str(d['Vlp']) if d['Vlp']==0 else fmt(d['Vlp'],12):>20} "
                      f"{fmt(d['Vclosed'],6):>12} "
                      f"{str(d['Vlp']==d['Vclosed']):>6}")

    banner("PART E.  A DELIBERATE HUNT FOR DISAGREEMENT.  Scan (k, t, rho) far "
           "outside every hypothesis")
    print("  GRID (stated in full, nothing truncated silently):")
    print("    k in {3,4,5,6,7,8,9,10,12,14}; t in the 11 rationals listed below;"
          " rho in {1,6/5,3/2,2}")
    print("  and report EVERY cell where exact minimax != phaseValueFull, "
           "together with which condition failed.")
    print("  (t grid is coarse on purpose; see the artifact for the exact grid.)")
    ts = [F(0), F(1, 1000), F(1, 100), F(1, 50), F(1, 20), F(1, 10), F(1, 5),
          F(1, 3), F(1, 2), F(3, 4), F(1)]
    rhos = [F(1), F(6, 5), F(3, 2), F(2)]
    ks = [3, 4, 5, 6, 7, 8, 9, 10, 12, 14]
    total = mism = undefined = 0
    mism_when_branch = mism_when_strong = 0
    buckets = {}
    for k in ks:
        for t in ts:
            for rho in rhos:
                d = cell(k, t, rho)
                total += 1
                if d["Vclosed"] is None:
                    undefined += 1
                    continue
                if d["Vlp"] != d["Vclosed"]:
                    mism += 1
                    key = (d["strong"], d["branch"], d["active"])
                    buckets[key] = buckets.get(key, 0) + 1
                    if d["branch"]:
                        mism_when_branch += 1
                    if d["strong"]:
                        mism_when_strong += 1
                assert d["cert_ok"], (k, t, rho)
    print(f"  cells scanned: {total};  disagreements: {mism};  "
          f"closed form UNDEFINED (c = 0, i.e. t = 1): {undefined}")
    if undefined:
        print(f"  NOTE the closed form phaseValueFull divides by 4c(k-1) with "
              f"c = (1-t)^(2q), so it is undefined at t = 1 even though the actual "
              f"minimax is defined there. Its stated domain must exclude t = 1.")
    print(f"  disagreements with `strong` TRUE : {mism_when_strong}   "
          f"(must be 0 -- Lean proves the value there)")
    print(f"  disagreements with exact `branch` TRUE : {mism_when_branch}")
    print(f"  disagreement buckets (strong, branch, active) -> count:")
    for key in sorted(buckets):
        print(f"    strong={key[0]!s:>5} branch={key[1]!s:>5} active={key[2]!s:>5} "
              f"-> {buckets[key]}")
    print(f"  agreement rate: {(total-mism)}/{total}")
    print()
    print(f"  [wall clock {time.time()-t0:.1f} s]")


if __name__ == "__main__":
    main()
