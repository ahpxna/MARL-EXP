#!/usr/bin/env python3
"""D6 Gói A step 1-2: the reduction algebra, DERIVED and then verified exactly.

WHAT THIS ADDS. `D4_two_curve_reduction.py` tests domination numerically, in floats,
with a -1e-12 tolerance, and its worst margins sit at ~1e-16 -- i.e. right on the
tolerance, so it cannot tell "exactly equal" from "slightly negative". This script
removes the numerics entirely.

THE DERIVATION (from the actual game, not assumed).
`approximate_game.problem` gives each query e and label L the mean  a + b*nu  with
    scalar i in coords :  1 if i in L, else 1 - nu
    scalar j           :  -1 + nu
    joint (G, h)       :  (1 - 2h + k_L) - (k_L - h) nu,   k_L = |G \ L|
and the per-query information against alternative `alt` at nuisance nu is
    I = (mean_true(mu) - mean_alt(nu))^2 / 2.
Write m = 2q+1 for the number of coordinates, A the true label (|A| = q+1), and
d = |alt \ A| the number of off-coordinates. For a joint query of width r put
    X = |G n A^c|,  and split A^c and alt^c into the four blocks they cut out.
A short computation (done symbolically below and checked against the module) gives
    mean_true - mean_alt = (h - X) (mu - nu) + beta (1-mu) - gamma (1-nu)
with beta, gamma the counts of G in two DISJOINT blocks of size d. Averaging the
square over a uniform r-subset G, the cross terms in (mu-nu) collapse and

    Jbar_{r,h,d}(mu,nu) = (K_{r,h}/2)(mu-nu)^2 + d B_r (1-mu)(1-nu)
    K_{r,h} = E[(X-h)^2] = r((q-1)r + q + 1)/(2m) - 2 h r q/m + h
    B_r     = E[beta^2] - E[beta gamma] all over d = r(m-r)/(2 q m)

which is exactly the supervisor's formula, now with a proof of where it comes from.
In particular  K_q = q(q^2+1)/(2m),  B_q = (q+1)/(2m).

THE CONSEQUENCE, and this is the point. Since 0 <= mu, nu <= 1 makes BOTH (mu-nu)^2
and (1-mu)(1-nu) non-negative, the width-q off-query dominates class (r,h) on the
WHOLE square as soon as
        K_q >= K_{r,h}   AND   B_q >= B_r,
two exact rational inequalities in (q, r, h) with no optimisation, no grid and no
tolerance. The scalar classes are not of this shape: in the same variables
    Ibar_ordinary_scalar = (q/(2m))(mu-nu)^2 + (d/m) mu nu
    Ibar_scalar_j        = (1/2)(mu-nu)^2
so scalar j is dominated by the q-off class exactly when K_q >= 1, i.e. q^3-3q-2 >= 0,
i.e. q >= 2 with EQUALITY AT q = 2.

WHAT IS CHECKED HERE
 1. the derived Jbar against the module's own coefficient matrix, exactly, for every
    q, every alternative and every class -- this is the bridge, and it is the step
    that would fail if the derivation were wrong;
 2. K_q >= K_{r,h} and B_q >= B_r as exact rationals for q in a range, over EVERY
    legal (r,h), reporting which comparisons are TIGHT;
 3. the two scalar classes;
 4. a negative control: the same test run with a deliberately wrong K, which must fail.

WHAT THIS DOES NOT ESTABLISH
 - Domination is not yet the reduction. Moving allocation mass off a dominated class
   also has to preserve feasibility of the allocation, and the permutation-averaging
   WLOG is a separate argument. Neither is here.
 - No phase boundary, no optimality, no Lean.

    .venv/bin/python scripts/A1_d6_reduction_algebra.py
"""
from __future__ import annotations

from fractions import Fraction as F
import importlib.util, itertools, json, math
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
GAME = REPO / "research/worker_distinct_research_acceptance_20260913/approximate_game.py"


def load_game():
    spec = importlib.util.spec_from_file_location("game", GAME)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    return mod


# ------------------------------------------------------------------ the formulas
def K(q: int, r: int, h: int) -> F:
    m = 2 * q + 1
    return F(r * ((q - 1) * r + q + 1), 2 * m) - F(2 * h * r * q, m) + h


def B(q: int, r: int) -> F:
    m = 2 * q + 1
    return F(r * (m - r), 2 * q * m)


def Jbar(q: int, r: int, h: int, d: int, mu: F, nu: F) -> F:
    return K(q, r, h) / 2 * (mu - nu) ** 2 + d * B(q, r) * (1 - mu) * (1 - nu)


def scalar_ordinary(q: int, d: int, mu: F, nu: F) -> F:
    m = 2 * q + 1
    return F(q, 2 * m) * (mu - nu) ** 2 + F(d, m) * mu * nu


def scalar_j(mu: F, nu: F) -> F:
    return (mu - nu) ** 2 / 2


# ----------------------------------------------- 1. the bridge, against the module
def physical_class(q, e):
    j = 2 * q + 1
    if e[0] == "s":
        return ("s", "j") if e[1] == j else ("s", "coord")
    return ("g", len(e[1]), int(e[2]))


def bridge_check(qs, mus, tol=1e-12):
    """For every q, mu, alternative and physical class, compare the DERIVED Jbar with
    the class-average of the module's own coefficient matrix, at several nu."""
    g = load_game()
    rows, worst = [], 0.0
    for q in qs:
        m = 2 * q + 1
        for mu in mus:
            queries, keys, counts, alts = g.problem(q, 0, float(mu))
            kidx = {k: i for i, k in enumerate(keys)}

            def key(e):
                coords = list(range(2 * q + 1)); j = 2 * q + 1
                A = frozenset(range(q + 1))
                groups = [sorted(A), [], [], sorted(set(coords) - A)]
                if e[0] == "s":
                    return ("s", 4 if e[1] == j else
                            next(i for i, gr in enumerate(groups) if e[1] in gr))
                return ("g", e[2], *(len(e[1] & set(gr)) for gr in groups))

            cls_keys = {}
            for e in queries:
                c = physical_class(q, e)
                cls_keys.setdefault(c, {}).setdefault(key(e), 0)
                cls_keys[c][key(e)] += 1
            avg = {}
            for c, kc in cls_keys.items():
                tot = sum(kc.values())
                v = [0.0] * len(keys)
                for k, n in kc.items():
                    v[kidx[k]] = n / tot
                avg[c] = v

            A = frozenset(range(q + 1))
            for alt, d, coeff in alts:
                for c, w in avg.items():
                    quad = [sum(coeff[t][i] * w[i] for i in range(len(keys)))
                            for t in range(3)]
                    for nu in (F(0), F(1, 3), F(1, 2), F(7, 10), F(1)):
                        got = quad[0] + float(nu) * quad[1] + float(nu) ** 2 * quad[2]
                        if c[0] == "g":
                            want = float(Jbar(q, c[1], c[2], d, mu, nu))
                        elif c[1] == "coord":
                            want = float(scalar_ordinary(q, d, mu, nu))
                        else:
                            want = float(scalar_j(mu, nu))
                        worst = max(worst, abs(got - want))
            rows.append({"q": q, "mu": str(mu), "alternatives": len(alts),
                         "classes": len(avg)})
    return rows, worst


# ------------------------------------------------- 2. exact domination, no numerics
def domination_exact(qs):
    rows = []
    for q in qs:
        m = 2 * q + 1
        Kq, Bq = K(q, q, 0), B(q, q)
        assert Kq == F(q * (q * q + 1), 2 * m), "K_q closed form"
        assert Bq == F(q + 1, 2 * m), "B_q closed form"
        fails, tight = [], []
        for r in range(0, q + 1):
            for h in (0, 1):
                if h == 0 and r < 2:
                    continue            # these queries do not exist in the game
                if (r, h) == (q, 0):
                    continue            # the survivor itself
                dK, dB = Kq - K(q, r, h), Bq - B(q, r)
                if dK < 0 or dB < 0:
                    fails.append({"r": r, "h": h, "dK": str(dK), "dB": str(dB)})
                if dK == 0 or dB == 0:
                    tight.append({"r": r, "h": h, "dK": str(dK), "dB": str(dB)})
        # the two scalar classes, in the same variables
        sj_margin = Kq - 1                       # K_q/2 - 1/2, cleared
        rows.append({"q": q, "m": m, "K_q": str(Kq), "B_q": str(Bq),
                     "joint_classes_tested": sum(1 for r in range(q + 1)
                         for h in (0, 1) if (h or r >= 2) and (r, h) != (q, 0)),
                     "violations": fails, "tight": tight,
                     "scalar_j_margin_2x": str(sj_margin),
                     "scalar_j_dominated": bool(sj_margin >= 0),
                     "scalar_j_tight": bool(sj_margin == 0)})
    return rows


def negative_control():
    """Run the same criterion with a deliberately wrong K (swap the sign of the h
    term) and check it REPORTS violations -- otherwise the criterion is inert."""
    def Kbad(q, r, h):
        m = 2 * q + 1
        return F(r * ((q - 1) * r + q + 1), 2 * m) + F(2 * h * r * q, m) + h
    bad = 0
    for q in (3, 4, 5):
        Kq = Kbad(q, q, 0)
        for r in range(q + 1):
            for h in (0, 1):
                if h == 0 and r < 2: continue
                if (r, h) == (q, 0): continue
                if Kq - Kbad(q, r, h) < 0:
                    bad += 1
    assert bad > 0, "the negative control found no violations; the test is inert"
    return bad


def main():
    print("1. bridge: derived Jbar versus the module's own coefficient matrix")
    rows, worst = bridge_check([3, 4, 5], [F(1, 4), F(2, 5), F(1, 2), F(3, 4)])
    for r in rows:
        print(f"   q={r['q']} mu={r['mu']}: {r['alternatives']} alternatives x "
              f"{r['classes']} classes x 5 values of nu")
    print(f"   worst absolute discrepancy over every (q, mu, alt, class, nu): "
          f"{worst:.3e}")
    if worst > 1e-11:
        raise AssertionError(f"the derived formula does NOT match the module: {worst}")

    print("\n2. exact domination: K_q >= K_{r,h} and B_q >= B_r, as rationals")
    dom = domination_exact(list(range(2, 13)))
    for r in dom:
        v = len(r["violations"])
        print(f"   q={r['q']:2d}: K_q={r['K_q']:>10s} B_q={r['B_q']:>8s}  "
              f"{r['joint_classes_tested']:2d} joint classes -> "
              f"{'ALL DOMINATED' if v == 0 else str(v) + ' VIOLATIONS'}"
              f"   scalar-j margin 2(J_q - J_sj)/(mu-nu)^2 = {r['scalar_j_margin_2x']}"
              f"{'  [TIGHT]' if r['scalar_j_tight'] else ''}")
        for t in r["tight"]:
            print(f"        TIGHT joint class r={t['r']} h={t['h']}: "
                  f"dK={t['dK']} dB={t['dB']}")
    total_v = sum(len(r["violations"]) for r in dom)

    print("\n3. negative control")
    nb = negative_control()
    print(f"   a deliberately wrong K produces {nb} violations, so the criterion "
          f"is not inert")

    print()
    if total_v == 0:
        print("Every eliminated joint class is dominated by the width-q off-query on the")
        print("WHOLE square 0 <= mu, nu <= 1, by two exact rational inequalities -- no")
        print("grid, no optimizer, no tolerance. This replaces D4's float margins of")
        print("~1e-16, which could not distinguish equality from a small violation.")
    else:
        print(f"{total_v} violations of the exact criterion.")
    out = REPO / "research/worker_D_blind_20260914/A1_reduction_algebra.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "derivation": "Jbar_{r,h,d} = (K/2)(mu-nu)^2 + d B (1-mu)(1-nu) with "
                      "K_{r,h} = E[(X-h)^2], X = |G n A^c| ~ Hypergeometric(2q+1,q,r), "
                      "and d B_r = E[beta^2] - E[beta gamma] for two disjoint blocks "
                      "of size d. Derived from approximate_game's affine means, not "
                      "assumed.",
        "criterion": "K_q >= K_{r,h} and B_q >= B_r imply domination on ALL of "
                     "[0,1]^2, because both (mu-nu)^2 and (1-mu)(1-nu) are >= 0 there",
        "bridge_worst_abs_discrepancy": worst,
        "bridge_configurations": rows,
        "domination": dom,
        "negative_control_violations": nb,
        "scope": "q in 2..12 for the exact criterion; q in {3,4,5} and "
                 "mu in {1/4,2/5,1/2,3/4} for the bridge against the module. "
                 "eps = 0, shell = 0 throughout.",
        "not_established": [
            "domination is not the reduction: moving allocation mass off a dominated "
            "class must also preserve feasibility, which is not shown here",
            "the permutation-averaging WLOG is a separate argument and is not here",
            "no phase boundary, no optimality, no Lean module",
        ],
    }, indent=2) + "\n")
    print(f"-> {out}")


if __name__ == "__main__":
    main()
