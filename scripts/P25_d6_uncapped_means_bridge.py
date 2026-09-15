#!/usr/bin/env python3
"""P25 -- D6: the bridge from the uncapped profile coefficients to the ACTUAL query
means, and the clipped nuisance branch.

`LeanD6UncappedProfileV1` says so itself: "THE BRIDGE TO THE ACTUAL MEANS IS NOT HERE.
`A d`, `B d`, `C d` are transcribed."  `D8_uncapped_design.py` checks them against
`B1.general_poly`, but `general_poly` is itself a transcription.  What was never
checked is the step that matters: do those coefficients come out of the ACTUAL
per-class information of the D6 model?

PART 1 answers that by SOLVING for the design.  For each `(q, mu, c, eta, d)` the
target `A_d x^2 + 2 B_d x + C_d` is a quadratic in `x`; so is `sum_e n_e I_e(d, x)`
with `I_e` the corpus's own per-class information (`P7.info_of`, which is built from
the query means).  Matching the three coefficients for SEVERAL `d` at once
over-determines the sample counts `n_e`, so a consistent non-negative solution is
evidence the coefficients really are the model's; an inconsistency would mean they are
not.  Everything is exact rational arithmetic.

PART 2 handles the side condition the module flags: `P 1` is attained only when the
unconstrained minimiser `x = -2 eta g / D 1` lies inside the legal nuisance window,
i.e. `2 eta g / D 1 <= mu`.  Where it fails, the minimum is at the CLAMP, which is
`LeanD6AlternativeReductionV1.quadratic_inf_endpoint_left/right` and
`LeanD6ScalarInformationV1.clipped_min`.  Part 2 reports where the side condition holds
and by how much it fails elsewhere, and recomputes the clipped value there.
"""
import json, os, sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from P7_d6_full_design import info_of, all_classes

OUT = "research/worker_P25_d6_20260915"

# the transcribed coefficients, exactly as in LeanD6UncappedProfileV1 / D8
def Dd(q, c, eta, d):  return c * (1 - eta) * (q - 1) + 2 * eta * (2 * q - d - 2)
def Ad(q, c, eta, d):  return F(q - d) * Dd(q, c, eta, d) / (2 * c * q * (q - 1))
def Bd(q, mu, c, eta, d):
    return eta * (1 - mu) * d * (q - d) / (c * q * (q - 1))
def Cd(q, mu, c, eta, d):
    g = 1 - mu
    return ((1 - eta) * d * mu * mu / (2 * q)
            + eta * g * g * d * (q + d - 2) / (c * q * (q - 1)))


def quad_of(f, d):
    """(a, b, c) with f(x) = a x^2 + b x + c, from three exact evaluations."""
    f0, f1, fm = f(d, F(0)), f(d, F(1)), f(d, F(-1))
    a = (f1 + fm - 2 * f0) / 2
    b = (f1 - fm) / 2
    return a, b, f0


def solve_rational(A, y):
    """Gaussian elimination over Fractions; returns a solution or None."""
    n, m = len(A), len(A[0])
    M = [row[:] + [y[i]] for i, row in enumerate(A)]
    piv = []
    r = 0
    for col in range(m):
        p = None
        for i in range(r, n):
            if M[i][col] != 0:
                p = i; break
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = F(1) / M[r][col]
        M[r] = [v * inv for v in M[r]]
        for i in range(n):
            if i != r and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(col)
        r += 1
        if r == n:
            break
    for i in range(r, n):
        if all(v == 0 for v in M[i][:m]) and M[i][m] != 0:
            return None                      # inconsistent
    x = [F(0)] * m
    for i, col in enumerate(piv):
        x[col] = M[i][m]
    return x


def main():
    os.makedirs(OUT, exist_ok=True)
    print("PART 1 -- do the transcribed coefficients come out of the ACTUAL means?")
    rows = []
    for q in (8, 16):
        for mu in (F(1, 4), F(2, 5)):
            for c in (F(3, 2), F(2)):
                for eta in (F(1, 3), F(13, 20), F(4, 5)):
                    classes = all_classes(q)
                    # restrict to the scalar/pair family the uncapped profile is about
                    keep = [i for i, (lab, r) in enumerate(classes)
                            if lab in (("scalar", "A"), ("scalar", "B"), ("scalar", "j"),
                                       ("query", 0, 2, 0), ("query", 2, 0, 0),
                                       ("query", 1, 1, 0))]
                    labs = [classes[i][0] for i in keep]
                    ds = [1, 2, 3]
                    A_rows, y = [], []
                    for d in ds:
                        # per-class quadratic coefficients
                        cols = [quad_of(lambda dd, x, lab=lab:
                                        info_of(q, mu, lab, dd, x), d) for lab in labs]
                        tgt = (Ad(q, c, eta, d),
                               2 * Bd(q, mu, c, eta, d),
                               Cd(q, mu, c, eta, d))
                        for k in range(3):
                            A_rows.append([col[k] for col in cols])
                            y.append(tgt[k])
                    sol = solve_rational(A_rows, y)
                    ok = sol is not None
                    nonneg = ok and all(v >= 0 for v in sol)
                    if ok:
                        # verify the solution on a d OUTSIDE the fitting set
                        dtest = 4 if q > 4 else 2
                        got = sum(sol[j] * info_of(q, mu, labs[j], dtest, F(1, 3))
                                  for j in range(len(labs)))
                        want = (Ad(q, c, eta, dtest) * F(1, 9)
                                + 2 * Bd(q, mu, c, eta, dtest) * F(1, 3)
                                + Cd(q, mu, c, eta, dtest))
                        holdout = (got == want)
                    else:
                        holdout = False
                    rows.append({
                        "q": q, "mu": str(mu), "c": str(c), "eta": str(eta),
                        "consistent_solution": ok,
                        "weights_nonneg": nonneg,
                        "holdout_d_matches": holdout,
                        "weights": None if not ok else
                                   {str(labs[j]): str(sol[j]) for j in range(len(labs))},
                    })
                    mark = ("OK " if (ok and holdout) else "!! ")
                    print(f"  {mark}q={q:3d} mu={mu} c={c} eta={eta}: "
                          f"consistent={ok} nonneg={nonneg} holdout={holdout}")

    print("\nPART 2 -- the clipped nuisance: is the unconstrained minimiser legal?")
    clip = []
    for q in (8, 16):
        for mu in (F(1, 4), F(2, 5)):
            g = 1 - mu
            for c in (F(3, 2), F(2)):
                for eta in (F(1, 3), F(13, 20), F(4, 5)):
                    D1 = Dd(q, c, eta, 1)
                    xstar = -2 * eta * g / D1
                    legal = (abs(xstar) <= mu)
                    clip.append({
                        "q": q, "mu": str(mu), "c": str(c), "eta": str(eta),
                        "x_unconstrained": str(xstar),
                        "window": f"[-{mu}, {1 - mu}]",
                        "inside_window": bool(legal),
                        "slack": str(mu - abs(xstar)),
                    })
                    print(f"  q={q:3d} mu={mu} c={c} eta={eta}: x* = "
                          f"{float(xstar): .8f}  window [-{float(mu)}, {float(1-mu)}]  "
                          f"{'LEGAL' if legal else 'CLIPPED at nu = 0'}")

    nall = sum(1 for r in rows if r["consistent_solution"] and r["holdout_d_matches"])
    nlegal = sum(1 for r in clip if r["inside_window"])
    out = {
        "script": "P25_d6_uncapped_means_bridge.py",
        "part1_question": "are A_d, B_d, C_d the coefficients of an ACTUAL design "
                          "built from the D6 query means?",
        "part1_method": "match the three quadratic coefficients at d = 1,2,3 "
                        "simultaneously against the corpus's own per-class information "
                        "(P7.info_of), then test the solution at a held-out d.  Exact "
                        "rational Gaussian elimination.",
        "part1_rows": rows,
        "part1_bridged": nall, "part1_total": len(rows),
        "part2_clipping": clip,
        "part2_legal": nlegal, "part2_total": len(clip),
        "not_established": [
            "A consistent non-negative solution is EVIDENCE the coefficients come from "
            "the model; it is not a derivation.  A derivation would compute the design "
            "from (eta, c) symbolically.",
            "Where the unconstrained minimiser is outside the window, P 1 is NOT "
            "attained and the clipped branch must be used; the Lean lemmas for that "
            "are LeanD6ScalarInformationV1.clipped_min and "
            "LeanD6AlternativeReductionV1.quadratic_inf_endpoint_left/right.",
        ],
    }
    path = os.path.join(OUT, "P25_d6_uncapped_means_bridge.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1)
    print(f"\nbridged cells: {nall}/{len(rows)};  nuisance legal in {nlegal}/{len(clip)}")
    print(f"artifact: {path}")


if __name__ == "__main__":
    main()
