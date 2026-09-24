#!/usr/bin/env python3
"""Paper C: figures C-F1 (exact price and phase boundary) and C-F2 (item-level stability).

NOTHING IS RE-SOLVED.  Every number drawn is read from an existing artifact under
`research/unified_20260919/` or is a closed formula transcribed from a Lean theorem.  The
script checks every stored number it draws against the proved formula it is drawn beside,
and refuses to write any figure if a check fails.

THE LEAN FORMULAS (all unconditional; `LeanPaperCEndgameV1`, `LeanPaperCEndpointLawV1`,
`LeanPaperCStabilityFamilyV1`):

    freeValue m        = 2 / ((m+4)(m-1))
    even_frontier_all  V_m(eta) = max(freeValue m, 4(1-eta)/(m(m+4)))    even m >= 4, eta >= 0
    etaStar m          = (m-2)/(2(m-1))                                   the even breakpoint
    odd_value_zero     V_m(0) = (m+3)/(m(m+4))                            odd m >= 3
    odd_breakpoint     V_m(eta) = freeValue m  <=>  eta >= 1              odd m >= 3
    family_value_robust
        |trueValue(g') - V_m(eta)| <= 3 ||g_m - g'||_1 / d,
        for 0 < d <= m+4 and d <= ||g'||_1, baseline RECOMPUTED for g' and normaliser
        MOVING to ||g'||_1, feasible item-band set held fixed.

WHAT EACH STORED QUANTITY IS (read from the producers, not assumed):

* `structural_frontier_corrected_v2.json` -- float LP optima of the paper's program at
  m = 5..9, NUMERICAL.  On the odd side only the two anchors are theorems; the curve between
  them is not, and it is drawn as a solved curve, not as a frontier.
* `paperC_flow_lp.json` -- breakpoints located by floating-point bisection on the flow LP at
  a SELECTED set of sizes (5..15, 17, 19, 21, 25, 31), not every integer through 31.
* `paperC_exact_dual.json` -- exact rational Farkas certificates, one per size, m = 5..11.
* `paperC_perturbation.json` -- `drift_movingD = |V(g'; recomputed baseline, D_1) - V(g_m)|`
  is the quantity `family_value_robust` bounds (`V_recomputed` in the group rows,
  `V_movingD` in the per-item rows).  `drift_fixedD` keeps the old normaliser and
  `drift_stale` keeps the old baseline; neither is the theorem's object, and both are drawn
  as diagnostics only.
* `paperC_robustness.json` -- `worst_ratio` is the SMALLEST price ratio an adversarial search
  found: an attained example, hence an UPPER bound on the worst case, never a lower
  certificate.  `proved_floor` is `price_ratio_robust`, in its stated domain (odd m,
  eps <= 1/4).  An attained ratio BELOW the floor would refute that theorem; attained ratios
  above it say nothing about how loose the floor is.

Outputs (new files; refuses to overwrite):
    research/papers/_figures/paperC_price_boundary.pdf     C-F1
    research/papers/_figures/paperC_stability.pdf          C-F2
    research/unified_20260919/paperC_endpoint_figures.json checks and provenance
"""

import hashlib
import json
import pathlib
import sys
from fractions import Fraction as Fr

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

SRC = pathlib.Path("research/unified_20260919")
OUT = pathlib.Path("research/papers/_figures")
FIG1 = OUT / "paperC_price_boundary.pdf"
FIG2 = OUT / "paperC_stability.pdf"
REC = SRC / "paperC_endpoint_figures.json"
INPUTS = ["structural_frontier_corrected_v2.json", "paperC_flow_lp.json",
          "paperC_breakpoint_certs.json", "paperC_exact_dual.json",
          "paperC_perturbation.json", "paperC_robustness.json"]

plt.rcParams.update({
    "font.size": 8, "axes.labelsize": 8, "axes.titlesize": 8.5,
    "legend.fontsize": 6.5, "xtick.labelsize": 7, "ytick.labelsize": 7,
    "figure.dpi": 200, "savefig.dpi": 200, "axes.grid": True,
    "grid.alpha": 0.25, "grid.linewidth": 0.5, "lines.linewidth": 1.2,
})

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def load(name):
    with open(SRC / name) as f:
        return json.load(f)


def tag(ax, text, x=0.99, y=0.02, ha="right"):
    ax.text(x, y, text, transform=ax.transAxes, ha=ha, va="bottom",
            fontsize=5.2, color="0.3",
            bbox=dict(boxstyle="round,pad=0.2", fc="white", ec="0.8", lw=0.4))


# ------------------------------------------------------------------ Lean formulas

def v_free(m):
    return Fr(2, (m + 4) * (m - 1))


def v_even(m, eta):
    return max(v_free(m), 4 * (1 - eta) / Fr(m * (m + 4)))


def eta_star_even(m):
    return Fr(m - 2, 2 * (m - 1))


def v_odd_zero(m):
    return Fr(m + 3, m * (m + 4))


def price_zero(m):
    """V_m(0)/V_free: odd from odd_value_zero, even from even_frontier_all at eta = 0."""
    return (v_odd_zero(m) if m % 2 else v_even(m, Fr(0))) / v_free(m)


def main():
    global FIG1, FIG2, REC
    if "--out" in sys.argv:
        d = pathlib.Path(sys.argv[sys.argv.index("--out") + 1])
        d.mkdir(parents=True, exist_ok=True)
        FIG1, FIG2, REC = d / FIG1.name, d / FIG2.name, d / REC.name
    for p in (FIG1, FIG2, REC):
        if p.exists():
            print(f"refusing to overwrite existing {p}", file=sys.stderr)
            return 2
    print("Paper C figures C-F1, C-F2: stored artifacts checked against the Lean formulas")

    fr = load("structural_frontier_corrected_v2.json")
    flow = load("paperC_flow_lp.json")
    certs = load("paperC_breakpoint_certs.json")
    farkas = load("paperC_exact_dual.json")
    pert = load("paperC_perturbation.json")
    rob = load("paperC_robustness.json")
    etas = [Fr(x).limit_denominator(1000) for x in fr["etas"]]

    # ---- C-F1 checks -------------------------------------------------------------
    worst_even, worst_anchor, odd_gap = 0.0, 0.0, []
    for ms, vals in fr["frontier"].items():
        m = int(ms)
        ok_free = Fr(fr["V_free"][ms]) == v_free(m)
        worst_anchor = max(worst_anchor, 0.0 if ok_free else 1.0)
        for eta, v in zip(etas, vals):
            if m % 2 == 0:
                worst_even = max(worst_even, abs(v - float(v_even(m, eta))))
            else:
                if eta == 0:
                    worst_anchor = max(worst_anchor, abs(v - float(v_odd_zero(m))))
                elif eta >= 1:
                    worst_anchor = max(worst_anchor, abs(v - float(v_free(m))))
                else:
                    odd_gap.append(v - float(v_free(m)))
    check("C-F1: at even m the float LP lies on even_frontier_all at every stored band",
          worst_even < 1e-7, f"sizes {[int(k) for k in fr['frontier'] if int(k) % 2 == 0]},"
          f" worst |LP - theorem| = {worst_even:.2e}")
    check("C-F1: at odd m the LP reproduces both proved anchors -- odd_value_zero at eta=0"
          " and freeValue at eta>=1 -- and the stored V_free strings equal 2/((m+4)(m-1))",
          worst_anchor < 1e-7, f"worst anchor deviation {worst_anchor:.2e}")
    check("C-F1: at odd m every stored band eta<1 is strictly above V_free, as the 'only"
          " if' half of odd_breakpoint requires", bool(odd_gap) and min(odd_gap) > 1e-9,
          f"{len(odd_gap)} points, smallest excess {min(odd_gap):.3e}")

    worst_flow = 0.0
    for r in flow["breakpoints"]:
        m = r["m"]
        pred = 1.0 if m % 2 else float(eta_star_even(m))
        worst_flow = max(worst_flow, abs(r["eta_star"] - pred))
    check("C-F1: the flow-LP bisection breakpoints agree with the theorems (etaStar for even"
          " m, 1 for odd m) at every stored size", worst_flow < 1e-4,
          f"sizes {[r['m'] for r in flow['breakpoints']]}, worst |bisection - theorem| ="
          f" {worst_flow:.1e}")
    fk_ok = all(Fr(r["conjecture"]) == (Fr(1) if r["m"] % 2 else eta_star_even(r["m"]))
                and r["root_matches_conjecture"] for r in farkas["rows"])
    check("C-F1: every Farkas certificate's root equals the proved breakpoint exactly",
          fk_ok, f"sizes {[r['m'] for r in farkas['rows']]}")
    o1_ok = all(Fr(r["free"]) == v_free(r["m"]) and Fr(r["value"]) == v_free(r["m"])
                and Fr(r["eta_star"]) == (Fr(1) if r["m"] % 2 else eta_star_even(r["m"]))
                for r in certs["O1_certificates"])
    check("C-F1: the rational per-size certificates at the breakpoint equal V_free and the"
          " proved breakpoint exactly", o1_ok,
          f"sizes {[r['m'] for r in certs['O1_certificates']]}")

    # ---- C-F2 checks -------------------------------------------------------------
    def lean_env(r):
        d = min(r["D0"], r["D1"])
        return 3.0 * r["l1"] / d, d

    grp, itm = pert["rows"], pert["per_item_rows"]
    hyp_ok, worst_ratio, n = True, 0.0, 0
    for r in grp + itm:
        env, d = lean_env(r)
        hyp_ok &= (d > 0) and abs(r["D0"] - (r["m"] + 4)) < 1e-12 and r["eta"] >= 0
        worst_ratio = max(worst_ratio, r["drift_movingD"] / env)
        n += 1
    check("C-F2: the stored normaliser of g_m is m+4 and d = min(D0, D1) meets"
          " family_value_robust's hypotheses 0 < d <= m+4, d <= ||g'||_1, eta >= 0", hyp_ok,
          f"{n} rows ({len(grp)} group, {len(itm)} per-item)")
    check("C-F2: EVERY stored perturbation of the theorem's object (recomputed baseline,"
          " moving normaliser) lies under 3||g_m - g'||_1/d -- a violation would refute"
          " family_value_robust", worst_ratio <= 1.0 + 1e-9,
          f"{n}/{n}; worst drift/envelope = {worst_ratio:.3f}")
    n_attempt_grp = 5 * 4 * 8
    n_attempt_itm = 3 * 4 * 5
    check("C-F2: no perturbation was silently dropped -- the producer skips solver failures"
          " without recording them, so the stored row counts are compared with its fixed"
          " grid (5 sizes x 4 bands x 8 radii; 3 sizes x 4 bands x 5 radii)",
          len(grp) == n_attempt_grp and len(itm) == n_attempt_itm,
          f"group {len(grp)}/{n_attempt_grp}, per-item {len(itm)}/{n_attempt_itm}")
    stale_over = sum(1 for r in grp if r["drift_stale"] > lean_env(r)[0])
    fixed_over = sum(1 for r in grp + itm if r["drift_fixedD"] > lean_env(r)[0])
    print(f"      diagnostics (not the theorem's object): stale baseline over the Lean"
          f" envelope at {stale_over}/{len(grp)}, fixed normaliser at {fixed_over}/{n}")

    rrows = rob["rows"]
    in_dom = [r for r in rrows if r["floor_in_domain"]]
    check("C-F2: every attained adversarial ratio in price_ratio_robust's domain is at or"
          " above the proved floor -- an attained ratio below it would refute the theorem;"
          " attained ratios above it are upper bounds on the worst case and do not measure"
          " the floor's slack", all(r["worst_ratio"] >= r["proved_floor"] - 1e-12
                                    for r in in_dom),
          f"{len(in_dom)} in-domain cells of {len(rrows)}")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print(f"\n{len(CHECKS) - nfail}/{len(CHECKS)} checks passed")
    if nfail:
        print("REFUSING to draw: a stored number disagrees with a proved formula.",
              file=sys.stderr)
        return 1

    # ---- C-F1 figure ------------------------------------------------------------
    fig, ax = plt.subplots(2, 2, figsize=(6.9, 4.6))
    a = ax[0, 0]
    grid = np.linspace(0, 1, 201)
    cols = plt.cm.viridis(np.linspace(0, 0.85, 5))
    for c, m in zip(cols, [4, 6, 8, 12, 20]):
        a.plot(grid, [float(v_even(m, Fr(x).limit_denominator(10 ** 6)) / v_free(m))
                      for x in grid], "-", color=c, label=f"$m={m}$")
        a.plot([float(eta_star_even(m))], [1.0], "|", color=c, ms=9, mew=1.5)
        if str(m) in fr["frontier"]:
            a.plot([float(e) for e in etas if e <= 1],
                   [v / float(v_free(m)) for e, v in zip(etas, fr["frontier"][str(m)])
                    if e <= 1], "o", color=c, ms=3.5, mfc="white")
    a.axhline(1.0, color="k", ls=":", lw=0.7)
    a.set_xlabel(r"band $\eta$"); a.set_ylabel(r"$V_m(\eta)/V_m^{\rm free}$")
    a.set_ylim(0.6, 2.0)
    a.set_title(r"even $m$: the whole frontier (ticks: $\eta_*$)")
    a.legend(frameon=False, ncol=2, loc="upper right")
    tag(a, "lines: THEOREM even_frontier_all (every even m>=4)\n"
           "open markers: NUMERICAL float LP, m=6,8")

    a = ax[0, 1]
    for c, m in zip(["#C44E52", "#DD8452", "#8172B3"], [5, 7, 9]):
        vals = fr["frontier"][str(m)]
        a.plot([float(e) for e in etas], [v / float(v_free(m)) for v in vals], "--o",
               color=c, ms=3, lw=0.8, mfc="white", label=f"$m={m}$ LP")
        a.plot([0.0], [float(price_zero(m))], "*", color=c, ms=9)
    a.plot([1.0, 3.0], [1.0, 1.0], "-", color="k", lw=2.2, alpha=0.6,
           label=r"$=V^{\rm free}$ iff $\eta\geq 1$")
    a.set_xlabel(r"band $\eta$"); a.set_ylabel(r"$V_m(\eta)/V_m^{\rm free}$")
    a.set_ylim(-0.4, 5.8)
    a.set_title("odd $m$: two proved anchors, not a curve")
    a.legend(frameon=False, loc="upper right")
    tag(a, "stars, bar: THEOREM odd_value_zero, odd_breakpoint\n"
           "dashed: NUMERICAL float LP (between the anchors: not proved)")

    a = ax[1, 0]
    ms_odd = list(range(3, 32, 2)); ms_even = list(range(4, 32, 2))
    a.plot(ms_odd, [float(price_zero(m)) for m in ms_odd], "o-", ms=3,
           color="#C44E52", label=r"odd: $(m+3)(m-1)/2m$")
    a.plot(ms_even, [float(price_zero(m)) for m in ms_even], "s-", ms=3,
           color="#4C72B0", label=r"even: $2(m-1)/m$")
    lp_m = sorted(int(k) for k in fr["frontier"])
    a.plot(lp_m, [fr["frontier"][str(m)][0] / float(v_free(m)) for m in lp_m], "x",
           color="k", ms=5, label="float LP, $m=5..9$")
    a.set_xlabel("$m$"); a.set_ylabel(r"$V_m(0)/V_m^{\rm free}$")
    a.set_title("the zero-band price, by parity")
    a.legend(frameon=False, loc="upper left")
    tag(a, "lines: THEOREM (every m); crosses: NUMERICAL", y=0.30)

    a = ax[1, 1]
    a.plot(ms_even, [float(eta_star_even(m)) for m in ms_even], "s-", ms=3,
           color="#4C72B0", label=r"even: $\eta_*=(m-2)/2(m-1)$")
    a.plot(ms_odd, [1.0] * len(ms_odd), "o-", ms=3, color="#C44E52",
           label=r"odd: $\eta_*=1$")
    fm = [r["m"] for r in flow["breakpoints"]]
    a.plot(fm, [r["eta_star"] for r in flow["breakpoints"]], "+", color="k", ms=6,
           label="flow-LP bisection (selected sizes)")
    km = [r["m"] for r in farkas["rows"]]
    a.plot(km, [float(Fr(r["conjecture"])) for r in farkas["rows"]], "D", mfc="none",
           color="#55A868", ms=5, label="exact Farkas certificate")
    a.set_ylim(0, 1.25)
    a.set_xlabel("$m$"); a.set_ylabel(r"breakpoint $\eta_*$")
    a.set_title("the phase boundary")
    a.legend(frameon=False, loc="center right", bbox_to_anchor=(1.0, 0.57), fontsize=5.8)
    tag(a, "lines: THEOREM; +: NUMERICAL; diamonds: EXACT per size")
    fig.tight_layout()
    fig.savefig(FIG1)
    plt.close(fig)

    # ---- C-F2 figure ------------------------------------------------------------
    fig, ax = plt.subplots(1, 3, figsize=(6.9, 2.45))
    a = ax[0]
    for rows, mk, lab in ((grp, "o", "group (flow LP)"), (itm, "^", "per item ($m!$ LP)")):
        e = np.array([lean_env(r)[0] for r in rows])
        dr = np.array([max(r["drift_movingD"], 1e-12) for r in rows])
        a.loglog(e, dr, mk, ms=3, mfc="none", label=lab)
    lim = [1e-4, 2.0]
    a.loglog(lim, lim, "k-", lw=0.8, label=r"$y=3\|g-g'\|_1/d$")
    a.fill_between(lim, lim, [10, 10], color="#C44E52", alpha=0.08)
    a.set_xlim(lim); a.set_ylim(1e-9, 2.0)
    a.set_xlabel(r"Lean envelope $3\|g_m-g'\|_1/d$"); a.set_ylabel("measured drift")
    a.set_title("the theorem's object (220 runs)")
    a.legend(frameon=False, loc="lower right", fontsize=5.8)
    tag(a, "NUMERICAL LP vs THEOREM\nfamily_value_robust\n(shaded: would refute it)", x=0.03, y=0.80, ha="left")

    a = ax[1]
    for key, mk, lab in (("drift_movingD", "o", "recomputed $b_k$, moving $D$ (theorem)"),
                         ("drift_fixedD", "s", "normaliser frozen at $D_0$"),
                         ("drift_stale", "x", "baseline frozen (group only)")):
        rows = grp if key == "drift_stale" else grp + itm
        a.semilogx([r["l1"] for r in rows],
                   [r[key] / lean_env(r)[0] for r in rows], mk, ms=3,
                   mfc="none" if mk != "x" else None, label=lab)
    a.axhline(1.0, color="k", lw=0.8)
    a.set_ylim(0, 1.3)
    a.set_xlabel(r"$\|g_m-g'\|_1$"); a.set_ylabel("drift / Lean envelope")
    a.set_title("which object moves")
    a.legend(frameon=False, loc="center right", bbox_to_anchor=(1.0, 0.60), fontsize=5.5)
    tag(a, "only the circles are the theorem's object", y=0.30)

    a = ax[2]
    for c, m in zip(["#C44E52", "#4C72B0", "#DD8452"], [5, 6, 7]):
        sub = [r for r in rrows if r["m"] == m]
        a.semilogy([r["eps"] for r in sub], [r["worst_ratio"] for r in sub], "o", color=c,
                   ms=3.5, mfc="none", label=f"$m={m}$ attained (search)")
        dom = [r for r in sub if r["floor_in_domain"]]
        if dom:
            a.semilogy([r["eps"] for r in dom], [r["proved_floor"] for r in dom], "-",
                       color=c, lw=1.4)
    a.set_xlabel(r"perturbation radius $\varepsilon=\|u\|_1$")
    a.set_ylabel(r"price ratio $V_{\rm unif}/V^{\rm free}$")
    a.set_title("attained vs proved floor")
    a.legend(frameon=False, loc="upper right", fontsize=5.5)
    a.set_ylim(0.3, 6.0)
    tag(a, "markers: ATTAINED (upper bounds on worst case)\n"
           "lines: THEOREM floor, odd m, eps<=1/4")
    fig.tight_layout()
    fig.savefig(FIG2)
    plt.close(fig)

    rec = {
        "producer": "scripts/FIG_paperC_endpoints.py",
        "producer_sha256": sha(__file__),
        "inputs_sha256": {name: sha(SRC / name) for name in INPUTS},
        "resolved_any_optimisation": False,
        "figures": [str(FIG1), str(FIG2)],
        "lean_formulas": {
            "freeValue": "2/((m+4)(m-1))", "even_frontier_all": "max(freeValue, 4(1-eta)/(m(m+4)))",
            "etaStar": "(m-2)/(2(m-1))", "odd_value_zero": "(m+3)/(m(m+4))",
            "odd_breakpoint": "V = freeValue iff eta >= 1",
            "family_value_robust": "|trueValue(g') - V_m(eta)| <= 3||g_m-g'||_1/d"},
        "diagnostics": {"stale_baseline_over_lean_envelope": stale_over,
                        "fixed_normaliser_over_lean_envelope": fixed_over,
                        "worst_drift_over_lean_envelope": worst_ratio},
        "checks": CHECKS, "all_passed": True,
    }
    with open(REC, "w") as f:
        json.dump(rec, f, indent=2)
    print(f"wrote {FIG1}, {FIG2}, {REC}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
