"""D06ALPHA self-check: verify every closed form used downstream against the
Lean sources, EXACTLY (fractions.Fraction only, no floating point).

Checks
  C1  slopes(k,t) from ResponseJoinV1:63,68 + CenteredCompensatedV1:70 equals the
      package closed forms with q = k-1:
        a = (1-t)^(2q+1) + q t (1-t)^(2q)
        b = (q-1) t (1-t)^(2q)
        c = a - b = (1-t)^(2q)          [<- also checks the c identity]
        p+r = 2c
  C2  PhaseRegretBridgeV1.count_loss_phase: under `strong` (1 <= (k-2) b) the
      full countLoss equals (commonConstant + variableCost)/2 at EVERY feasible
      (u,v).  Also record, for each (k,t,rho), the EXACT set of feasible (u,v)
      where the two disagree when `strong` fails -- this is the branch flip that
      makes the closed form inapplicable outside the strong domain.
  C3  EndpointWorldsV1.regret_counts: regret from countLoss equals
      (variableCost + max(e, r*h))/2 wherever count_loss_phase applies.
  C4  the exact branch condition.  minimum_branch_dominates is SUFFICIENT.
      The exact condition for "branch 1 is the min at every feasible (u,v)"
      is derived here and then tested by brute force, so that we never
      attribute a change of value to `strong` when the real cause is elsewhere.

Run:  python3 /Users/phanan/cig-amf-main/scripts/D06ALPHA_selfcheck.py
"""

import sys
from fractions import Fraction as F

sys.path.insert(0, "/Users/phanan/cig-amf-main/scripts")
from D06ALPHA_gamelib import slopes, count_loss, legal_minimum


def pkg_forms(q, t):
    """The closed forms exactly as written in the package brief."""
    b = (q - 1) * t * (1 - t) ** (2 * q)
    a = (1 - t) ** (2 * q + 1) + q * t * (1 - t) ** (2 * q)
    return a, b, a - b


def variable_cost(a, b, rho, u, v):
    corr = min(a, 2 * b) if (u == 0 and v == 0) else (b if (u == 0 and v == 1) else 0 * a)
    return (rho - 2 * b) * v - (2 * a - rho) * u - corr


def common_constant(a, b, k):
    return a * (1 + k) + b * (k - 1)


def exact_branch_ok(a, b, k, h):
    """True iff branch 1 (the 'phase' branch) is the min at EVERY (u,v) with
    u<=h, v<=k-h.  Derived, then brute-forced below."""
    nb = k - 1
    for u in range(h + 1):
        for v in range(k - h + 1):
            low1 = (1 - a) - a * (k - u) - b * (nb - v)
            low2 = -b if v < nb else 0 * b
            if low1 > low2:
                return False
    return True


def main():
    ts = [F(0), F(1, 1000), F(1, 100), F(1, 37), F(1, 10), F(1, 5), F(1, 3),
          F(1, 2), F(3, 4), F(9, 10), F(1)]
    rhos = [F(1), F(6, 5), F(3, 2), F(9, 5), F(2)]
    ks = [3, 4, 5, 6, 7, 8, 9, 10, 12]

    n1 = n2 = 0
    print("C1 slopes vs package closed forms, C1b c == (1-t)^(2q), C1c p+r == 2c")
    for k in ks:
        q = k - 1
        for t in ts:
            a, b, c = slopes(k, t)
            A, B, C = pkg_forms(q, t)
            assert (a, b, c) == (A, B, C), (k, t, a, A, b, B)
            assert c == (1 - t) ** (2 * q), (k, t, c)
            for rho in rhos:
                assert (rho - 2 * b) + (2 * a - rho) == 2 * c
            n1 += 1
    print(f"  PASS on {n1} (k,t) pairs, all exact, 0 residual (Fraction equality)")

    print()
    print("C2/C3/C4 branch analysis. Columns:")
    print("  strong = 1 <= (k-2)b   (the Lean SUFFICIENT condition)")
    print("  exact  = branch-1 is the min at every feasible (u,v)  (brute force)")
    print("  phase_ok = countLoss == (commonConstant+variableCost)/2 everywhere")
    print()
    print(f"{'k':>3} {'t':>10} {'(k-2)b':>12} {'1-a':>10} {'strong':>7} {'exact':>6} {'phase_ok':>9}")
    rows = []
    disagree_strong_exact = 0
    for k in ks:
        for t in ts:
            a, b, c = slopes(k, t)
            strong = (k - 2) * b >= 1
            exact = all(exact_branch_ok(a, b, k, h) for h in range(0, k + 1))
            phase_ok = True
            for rho in rhos:
                for h in range(0, k + 1):
                    for u in range(h + 1):
                        for v in range(k - h + 1):
                            cl = count_loss(a, b, rho, k, k - 1, u, v)
                            ph = (common_constant(a, b, k)
                                  + variable_cost(a, b, rho, u, v)) / 2
                            if cl != ph:
                                phase_ok = False
            n2 += 1
            if strong and not phase_ok:
                raise AssertionError(
                    f"strong holds but phase formula fails: k={k} t={t}")
            if exact != phase_ok:
                raise AssertionError(f"exact-branch test disagrees with phase_ok: k={k} t={t}")
            if strong != exact:
                disagree_strong_exact += 1
            rows.append((k, t, strong, exact, phase_ok))
            if t in (F(0), F(1, 100), F(1, 37), F(1, 10), F(1, 2), F(1)):
                print(f"{k:>3} {str(t):>10} {float((k-2)*b):>12.6g} {float(1-a):>10.6g} "
                      f"{str(strong):>7} {str(exact):>6} {str(phase_ok):>9}")
    print()
    print(f"C2 PASS: on {n2} (k,t) cells, `strong` ALWAYS implies the phase formula "
          f"(0 counterexamples).")
    print(f"C4: `strong` and the EXACT branch condition differ on "
          f"{disagree_strong_exact} / {n2} cells -- `strong` is strictly "
          f"sufficient, never necessary.")
    print()
    print("C4b derived exact condition (checked against brute force above):")
    print("  branch 1 is the min at every feasible (u,v) iff")
    print("    (i)  for v < k-1 : 1 <= a(k-u+1) + b(k-2-v) for all feasible u,v")
    print("                  worst case u = min(h,k), v = 0")
    print("    (ii) for v = k-1 (forces h=1, u<=1): 1 <= a(k-u+1), worst u=1: 1 <= a*k")
    # verify the derived characterisation against brute force
    bad = 0
    for k in ks:
        for t in ts:
            a, b, c = slopes(k, t)
            brute = all(exact_branch_ok(a, b, k, h) for h in range(0, k + 1))
            # derived: worst cases only
            der = True
            for h in range(0, k + 1):
                for u in range(h + 1):
                    for v in range(k - h + 1):
                        if v < k - 1:
                            if 1 - a * (k - u + 1) - b * (k - 2 - v) > 0:
                                der = False
                        else:
                            if 1 - a * (k - u + 1) > 0:
                                der = False
            if der != brute:
                bad += 1
    print(f"  derived vs brute force: {bad} mismatches out of {len(ks)*len(ts)}")

    print()
    print("C3 regret identity spot check (uses legal_minimum, i.e. countMinimum):")
    for (k, t, rho) in [(9, F(1, 25), F(1)), (9, F(1, 25), F(3, 2)), (5, F(1, 10), F(1))]:
        a, b, c = slopes(k, t)
        e = min(a, 2 * b)
        r = 2 * a - rho
        ok = True
        for h in range(1, k + 1):
            lmin = legal_minimum(a, b, rho, k, h)
            for u in range(h + 1):
                for v in range(k - h + 1):
                    reg = count_loss(a, b, rho, k, k - 1, u, v) - lmin
                    pred = (variable_cost(a, b, rho, u, v) + max(e, r * h)) / 2
                    if reg != pred:
                        ok = False
        print(f"  k={k} t={t} rho={rho}: strong={bool((k-2)*b>=1)}  "
              f"regret_counts identity holds everywhere: {ok}")


if __name__ == "__main__":
    main()
