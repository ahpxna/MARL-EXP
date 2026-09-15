#!/usr/bin/env python3
"""D6: is the two-curve reduction TRUE, or only what the solver happened to find?

The closed-form blind phase boundary of `D3_blind_phase_boundary.py` is derived
from the hypothesis that, after averaging over the symmetry group, the blind
optimum needs only two physical query classes: the ordinary scalar, and the
width-q off-query (`h = false`). That hypothesis has NOT been proved, and
"the LP only put mass on two classes" is not an argument -- a dominated class
carries no mass either way.

QUANTIFIER ORDER, which the previous version of this probe got wrong. To move
allocation mass off class `c` one needs ONE replacement that works against every
alternative at once,

    EXISTS s  FORALL a, nu :   Ibar_s(a, nu) >= Ibar_c(a, nu),

or, more generally, one MIXTURE theta over the survivors used for every
alternative. The earlier version chose the best survivor separately for each
alternative, i.e. it tested

    FORALL a  EXISTS s  FORALL nu : ...,

which is strictly weaker and does not justify the reduction. `counterexample_control`
below exhibits the gap concretely: with I_s1 = (1,0), I_s2 = (0,1) and
I_c = (3/4,3/4) on two alternatives the weak test passes, yet deleting `c` drops
the minimax value from 3/4 to 1/2. That is a counterexample to the TEST, not to
the D6 conjecture.

This probe therefore reports three numbers per class: the weak per-alternative
margin (for contrast only), the uniform single-survivor margin, and a mixture
certificate. The mixture is SEARCHED with an LP on a nu grid and then VERIFIED
without any optimizer and without any grid, by minimising the resulting quadratic
in nu on [0,1] in closed form. Only the verified mixture margin decides.

    .venv/bin/python scripts/D4_two_curve_reduction.py
"""
from __future__ import annotations

import importlib.util, json
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parents[1]
GAME = REPO / "research/worker_distinct_research_acceptance_20260913/approximate_game.py"


def load_game():
    spec = importlib.util.spec_from_file_location("game", GAME)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
    return m


def physical_class(q, e):
    j = 2 * q + 1
    if e[0] == "s":
        return ("s", "j") if e[1] == j else ("s", "coord")
    return ("g", len(e[1]), bool(e[2]))


def analyse(g, q, mu):
    queries, keys, counts, alts = g.problem(q, 0, mu)
    coords = list(range(2 * q + 1)); j = 2 * q + 1
    A = frozenset(range(q + 1)); B = A
    groups = [sorted(A & B), sorted(A - B), sorted(B - A), sorted(set(coords) - (A | B))]

    def key(e):
        if e[0] == "s":
            return ("s", 4 if e[1] == j else
                    next(i for i, gr in enumerate(groups) if e[1] in gr))
        return ("g", e[2], *(len(e[1] & set(gr)) for gr in groups))

    kidx = {k: i for i, k in enumerate(keys)}
    # physical class -> the count-weighted average vector over its orbit keys
    cls_keys = {}
    for e in queries:
        cls_keys.setdefault(physical_class(q, e), {}).setdefault(key(e), 0)
        cls_keys[physical_class(q, e)][key(e)] += 1
    avg = {}
    for c, kc in cls_keys.items():
        tot = sum(kc.values())
        v = np.zeros(len(keys))
        for k, n in kc.items():
            v[kidx[k]] = n / tot
        avg[c] = v

    target = ("g", q, False)
    if target not in avg:
        raise AssertionError(f"the width-{q} off-query class is absent at q={q}")

    coeff = np.array([a[2] for a in alts])          # (alts, 3, keys)
    dom_fail, checked = [], 0
    worst_margin = None

    def quad_min_on_unit(C, B, A):
        """exact-in-spirit minimum of C + B nu + A nu^2 on [0,1]: endpoints, plus
        the vertex when it lies inside. No grid."""
        cands = [C, C + B + A]
        if A > 0:
            v = -B / (2 * A)
            if 0.0 < v < 1.0:
                cands.append(C + B * v + A * v * v)
        return min(cands)

    scalar = ("s", "coord")
    survivors = [target] + ([scalar] if scalar in avg else [])
    nalt = len(alts)
    TOL = -1e-12
    nu_grid = np.linspace(0.0, 1.0, 21)
    P = {c: coeff @ avg[c] for c in avg}          # class -> (alts, 3) quadratics

    def min_over_nu(D):
        """min over nu in [0,1], one entry per alternative. Closed form."""
        return np.array([quad_min_on_unit(D[a, 0], D[a, 1], D[a, 2])
                         for a in range(nalt)])

    per_class = []
    for c in sorted(avg, key=str):
        if c in survivors:
            continue    # the two SURVIVING classes are not to be eliminated
        Mar = {s: min_over_nu(P[s] - P[c]) for s in survivors}
        checked += nalt * len(survivors)
        # (i) the WEAK test the earlier version ran: survivor chosen PER alternative
        weak = float(min(max(Mar[s][a] for s in survivors) for a in range(nalt)))
        # (ii) the correct single-survivor test: one s good for EVERY alternative
        uni = {s: float(Mar[s].min()) for s in survivors}
        best_s = max(uni, key=lambda s: uni[s])
        uniform = uni[best_s]
        # (iii) one MIXTURE of the survivors, used for every alternative
        theta, mix = mixture_certificate(P, survivors, c, nu_grid, min_over_nu)
        row = {"class": str(c), "is_scalar_class": c[0] == "s",
               "weak_per_alternative_margin": weak,
               "uniform_single_survivor_margin": uniform,
               "best_single_survivor": str(best_s),
               "mixture_theta": None if theta is None else [float(t) for t in theta],
               "mixture_verified_margin": None if mix is None else float(mix),
               "eliminable": bool(mix is not None and mix >= TOL)}
        per_class.append(row)
        if not row["eliminable"]:
            dom_fail.append(row)
        m = mix if mix is not None else -float("inf")
        if worst_margin is None or m < worst_margin:
            worst_margin = m
    return {"q": q, "mu": mu,
            "classes_compared": len(avg) - len(survivors),
            "survivors": [str(x) for x in survivors],
            "joint_classes": len([c for c in avg if c[0] == "g"]),
            "scalar_classes": len([c for c in avg if c[0] == "s"]),
            "comparisons": checked,
            "violations": len(dom_fail),
            "violations_scalar": len([d for d in dom_fail if d["is_scalar_class"]]),
            "worst_margin": float(worst_margin) if worst_margin is not None else None,
            "weak_test_would_pass_all": all(r["weak_per_alternative_margin"] >= TOL
                                            for r in per_class),
            "uniform_test_passes_all": all(r["uniform_single_survivor_margin"] >= TOL
                                           for r in per_class),
            "per_class": per_class,
            "examples": dom_fail[:5]}


def mixture_certificate(P, survivors, c, nu_grid, min_over_nu):
    """Search a single mixture `theta` over the survivors with
    sum_s theta_s Ibar_s(a,nu) >= Ibar_c(a,nu) for EVERY alternative and nu, then
    VERIFY it. The LP below is only the search: it uses a nu grid and floats. The
    number that is reported is the verification, which uses no optimizer and no
    grid -- the margin is a quadratic in nu and its minimum on [0,1] is taken at
    an endpoint or at the vertex."""
    from scipy.optimize import linprog
    pc, ps = P[c], [P[s] for s in survivors]
    ns, nalt = len(survivors), pc.shape[0]
    A_ub, b_ub = [], []
    for a in range(nalt):
        for nu in nu_grid:
            v = [p[a, 0] + p[a, 1] * nu + p[a, 2] * nu * nu for p in ps]
            vc = pc[a, 0] + pc[a, 1] * nu + pc[a, 2] * nu * nu
            A_ub.append([-x for x in v] + [1.0])      # -theta.v + t <= -vc
            b_ub.append(-vc)
    res = linprog(c=[0.0] * ns + [-1.0], A_ub=A_ub, b_ub=b_ub,
                  A_eq=[[1.0] * ns + [0.0]], b_eq=[1.0],
                  bounds=[(0.0, None)] * ns + [(None, None)], method="highs")
    if not res.success:
        return None, None
    theta = np.asarray(res.x[:ns], dtype=float)
    theta = np.clip(theta, 0.0, None)
    tot = theta.sum()
    if tot <= 0:
        return None, None
    theta = theta / tot                                # exact feasibility of theta
    D = sum(t * p for t, p in zip(theta, ps)) - pc
    return theta, float(min_over_nu(D).min())


def counterexample_control():
    """The weak test accepts an instance where deleting the class LOWERS the
    minimax value. I_s1 = (1,0), I_s2 = (0,1), I_c = (3/4,3/4), constant in nu."""
    I = {"s1": np.array([1.0, 0.0]), "s2": np.array([0.0, 1.0])}
    Ic = np.array([0.75, 0.75])
    weak = float(min(max(I["s1"][a], I["s2"][a]) - Ic[a] for a in (0, 1)))
    uniform = float(max(min(I[s][a] - Ic[a] for a in (0, 1)) for s in I))
    th = np.linspace(0.0, 1.0, 100001)
    mixture = float(np.max(np.minimum(th - 0.75, (1 - th) - 0.75)))
    value_with_c = 0.75                  # put all mass on c
    value_without_c = float(np.max(np.minimum(th, 1 - th)))
    assert weak >= 0.0, "the weak test no longer passes this instance"
    assert uniform < 0.0 and mixture < 0.0, "the correct tests no longer reject it"
    assert value_without_c < value_with_c, "deleting c no longer lowers the value"
    return weak, uniform, mixture, value_with_c, value_without_c


def main():
    w, u, mx, vc, vnc = counterexample_control()
    print("control (the defect in the previous test design):")
    print(f"  I_s1=(1,0) I_s2=(0,1) I_c=(3/4,3/4): weak per-alternative margin "
          f"{w:+.3f} (PASSES), uniform single-survivor {u:+.3f}, best mixture "
          f"{mx:+.3f} (both REJECT)")
    print(f"  and deleting c really does lower the minimax value: {vc} -> {vnc}\n")
    g = load_game()
    rows = []
    for q in (3, 4, 5):
        for mu in (0.25, 0.5, 0.75):
            r = analyse(g, q, mu)
            rows.append(r)
            verdict = ("ELIMINABLE" if r["violations"] == 0
                       else f"{r['violations']} CLASSES NOT ELIMINABLE")
            print(f"q={q} mu={mu}: {r['joint_classes']} joint + "
                  f"{r['scalar_classes']} scalar classes, {r['comparisons']} "
                  f"comparisons -> {verdict}   worst VERIFIED mixture margin over "
                  f"ALL nu in [0,1]: {r['worst_margin']:+.3e}"
                  f"   [weak test would pass all: {r['weak_test_would_pass_all']}; "
                  f"uniform single survivor suffices: {r['uniform_test_passes_all']}]")
            for ex in r["examples"]:
                print(f"    NOT eliminable: class {ex['class']}: uniform "
                      f"{ex['uniform_single_survivor_margin']:+.6e}, mixture "
                      f"{ex['mixture_verified_margin']}"
                      + ("  [SCALAR class]" if ex["is_scalar_class"] else ""))
    total_v = sum(r["violations"] for r in rows)
    print()
    if total_v == 0:
        print("every class OUTSIDE the two survivors {ordinary scalar, width-q "
              "off-query} is dominated by ONE mixture of them that is the same for "
              "EVERY alternative, over ALL of nu in [0,1].")
        print("the quantifier order is now EXISTS mixture FORALL (alt, nu). The "
              "mixture is found by an LP on a nu grid and then verified with no "
              "optimizer and no grid, by minimising the quadratic in nu on [0,1] at "
              "its endpoints and vertex. Still float arithmetic with a -1e-12 "
              "tolerance, still only the (q, mu) cells listed, and the coefficient "
              "matrix still comes from the solver module.")
    else:
        print(f"{total_v} classes are NOT eliminable by any single mixture of the "
              "two survivors. Under the correct quantifier order the two-curve "
              "reduction is therefore NOT established by this probe, and the "
              "closed-form boundary derived from it keeps only the weaker support.")
    out = REPO / "research/worker_D_blind_20260914/D4_two_curve_reduction.json"
    out.write_text(json.dumps({
        "hypothesis": "after group averaging the blind optimum needs only the "
                      "ordinary scalar and the width-q off-query",
        "test": "EXISTS one mixture theta over the two SURVIVORS (ordinary scalar, "
                "width-q off-query), the SAME mixture for every alternative, with "
                "sum_s theta_s Ibar_s(a,nu) >= Ibar_c(a,nu) FORALL alternatives a "
                "and ALL nu in [0,1]. theta is searched by an LP on a nu grid and "
                "then VERIFIED off-grid and optimizer-free: the margin is quadratic "
                "in nu and its minimum on [0,1] is at an endpoint or the vertex",
        "quantifier_order_correction": "the previous version chose the best "
                "survivor SEPARATELY FOR EACH ALTERNATIVE, i.e. it tested FORALL a "
                "EXISTS s FORALL nu, which is strictly weaker and cannot justify "
                "moving allocation mass. counterexample_control() exhibits "
                "I_s1=(1,0), I_s2=(0,1), I_c=(3/4,3/4): the weak test passes, both "
                "correct tests reject, and deleting c lowers the minimax value from "
                "3/4 to 1/2. That refutes the TEST, not the D6 conjecture.",
        "test_design_correction": "an earlier version asked whether the width-q "
                "class dominates the ordinary scalar too. It does not, and it "
                "should not: the scalar is one of the two survivors, and the "
                "failures appeared exactly at mu = 0.75, which is ABOVE the phase "
                "boundary mu*(q) where the scalar is supposed to enter. The wrong "
                "test was reporting the mechanism as a refutation.",
        "rows": rows, "total_violations": total_v,
        "scope": "q in {3,4,5}, mu in {0.25,0.5,0.75}, eps=0 shell=0. All nu in "
                 "[0,1] via the quadratic minimum, no grid. Float arithmetic with a "
                 "-1e-12 tolerance -- not an exact rational certificate. The "
                 "coefficient matrix itself comes from the solver module.",
    }, indent=2) + "\n")
    print(f"-> {out}")


if __name__ == "__main__":
    main()
