#!/usr/bin/env python3
"""Paper C, figure C-F3: the three closed-form results, drawn from the theorems.

(a) the whole frontier `V_m(eta)/V_free` (`even_frontier_all`, `odd_frontier`), with the
float LP values of `paperC_formula_check.json` as cross-check markers;
(b) the banded ex-post value over the free ex-post value (`expost_even`, `expost_odd`), same;
(c) the collapse scale at m = 101, theorem curves only: the proved floor of
`physical_price_ratio` with d = m + 4 - eps, the linear guarantee `(m-1)/4` of
`physical_price_linear` at eps <= 1/2m, the lower side `1/(16 eps)` of `collapse_lower` on
[1/m, 1/6], and the construction `10/eps` of `collapse_upper`.

Curves are the formulas.  Markers are numerical and only cross-check them.

SELF-CHECKS (refuse to draw): the input passed its checks and names its producer; every
stored LP value equals the formula within 1e-7, recomputed here; the proved floor lies below
the construction's upper bound wherever both are drawn (a theorem-consistency check that
would fail on a transcription error).

Outputs (new files; refuse to overwrite):
    research/papers/_figures/paperC_theorems.pdf
    research/unified_20260919/paperC_theorems_figure.json
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
FIG = pathlib.Path("research/papers/_figures/paperC_theorems.pdf")
REC = SRC / "paperC_theorems_figure.json"
INPUT = "paperC_formula_check.json"
plt.rcParams.update({"font.size": 8, "axes.labelsize": 8, "axes.titlesize": 8.5,
                     "legend.fontsize": 5.8, "xtick.labelsize": 7, "ytick.labelsize": 7,
                     "figure.dpi": 200, "savefig.dpi": 200, "axes.grid": True,
                     "grid.alpha": 0.25, "grid.linewidth": 0.5})
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def v_free(m):
    return 2 / ((m + 4) * (m - 1))


def frontier(m, eta):
    if m % 2 == 0:
        return max(v_free(m), 4 * (1 - eta) / (m * (m + 4)))
    return max((m + 3 - (m + 1) * eta) / (m * (m + 4)),
               v_free(m) + max(0.0, 1 - eta) / (m * (m + 4)))


def expost(m, eta):
    if m % 2 == 0:
        return 2 / (m + 4)
    return (2 + 2 * max(0.0, 1 - eta) / m) / (m + 4)


def floor_ratio(m, eps):
    d = m + 4 - eps
    v0 = (m + 3) / (m * (m + 4))
    num = v0 - 3 * eps / d
    return num / (v_free(m) + 3 * eps / d) if num > 0 else np.nan


def main():
    global FIG, REC
    if "--out" in sys.argv:
        d = pathlib.Path(sys.argv[sys.argv.index("--out") + 1])
        d.mkdir(parents=True, exist_ok=True)
        FIG, REC = d / FIG.name, d / REC.name
    for p in (FIG, REC):
        if p.exists():
            print(f"refusing to overwrite existing {p}", file=sys.stderr)
            return 2
    src = json.load(open(SRC / INPUT))
    check("the input passed its own checks and names its producer",
          src["all_passed"] and src["producer"] == "scripts/EXP_paperC_formula_check.py")
    gap = max(max(abs(r["lp_exante"] - frontier(r["m"], r["eta"])),
                  abs(r["lp_expost"] - expost(r["m"], r["eta"]))) for r in src["rows"])
    check("every stored LP value equals the formula, recomputed here", gap < 1e-7,
          f"largest gap {gap:.1e}")
    M = 101
    eps = np.logspace(-4, 0, 400)
    fl = np.array([floor_ratio(M, e) for e in eps])
    up = 10 / eps
    both = ~np.isnan(fl) & (eps >= 1 / M)
    check("theorem consistency at m = 101: proved floor <= construction bound where both apply",
          bool(np.all(fl[both] <= up[both] + 1e-12)))
    if not all(c["ok"] for c in CHECKS):
        print("REFUSING to draw.", file=sys.stderr)
        return 1

    fig, ax = plt.subplots(1, 3, figsize=(6.9, 2.45))
    et = np.linspace(0, 1.6, 401)
    cols = {5: "#C44E52", 7: "#DD8452", 9: "#8172B2", 4: "#4C72B0", 6: "#55A868", 8: "#64B5CD"}
    a = ax[0]
    for m in (5, 7, 9, 4, 6, 8):
        a.plot(et, [frontier(m, e) / v_free(m) for e in et], color=cols[m],
               ls="-" if m % 2 else "--", lw=1.1, label=f"m={m}")
        pts = [r for r in src["rows"] if r["m"] == m]
        a.plot([r["eta"] for r in pts], [r["lp_exante"] / v_free(m) for r in pts], "o",
               color=cols[m], ms=2.2, mfc="none", mew=0.6)
    a.set_xlabel(r"band width $\eta$"); a.set_ylabel(r"$V_m(\eta)/V^{\rm free}_m$")
    a.set_title("ex ante: the whole frontier")
    a.legend(frameon=False, ncol=2, loc="upper right")
    a = ax[1]
    for m in (3, 5, 7, 9, 4, 6):
        c = cols.get(m, "#937860")
        a.plot(et, [expost(m, e) / (2 / (m + 4)) for e in et], color=c,
               ls="-" if m % 2 else "--", lw=1.1, label=f"m={m}")
        pts = [r for r in src["rows"] if r["m"] == m]
        a.plot([r["eta"] for r in pts], [r["lp_expost"] / (2 / (m + 4)) for r in pts], "o",
               color=c, ms=2.2, mfc="none", mew=0.6)
    a.set_ylim(0.95, 1.4)
    a.set_xlabel(r"band width $\eta$"); a.set_ylabel(r"$V^{\rm post}_m(\eta)\,/\,\frac{2}{m+4}$")
    a.set_title("ex post: the band is almost free")
    a.legend(frameon=False, ncol=2, loc="upper right")
    a = ax[2]
    a.loglog(eps, fl, color="k", lw=1.1, label="proved floor (every $g'$)")
    lin = eps <= 1 / (2 * M)
    a.loglog(eps[lin], np.full(lin.sum(), (M - 1) / 4), color="#55A868", lw=2.0,
             label=r"every $g'$: $(m-1)/4$, $\varepsilon\leq 1/2m$")
    lo = (eps >= 1 / M) & (eps <= 1 / 6)
    a.loglog(eps[lo], 1 / (16 * eps[lo]), color="#4C72B0", lw=2.0,
             label=r"every $g'$: $1/16\varepsilon$ on $[1/m,1/6]$")
    a.loglog(eps, up, color="#C44E52", ls="--", lw=1.1, label=r"one construction: $10/\varepsilon$")
    a.axhline((M + 3) * (M - 1) / (2 * M), color="0.5", ls=":", lw=0.8)
    a.set_ylim(0.5, 200)
    a.set_xlabel(r"perturbation size $\varepsilon=\|g_m-g'\|_1$")
    a.set_ylabel("price ratio")
    a.set_title(r"worst price over the ball, $m=101$ (theorems)")
    a.legend(frameon=False, loc="lower left", fontsize=5.2)
    fig.tight_layout()
    fig.savefig(FIG)
    plt.close(fig)
    rec = {"producer": "scripts/FIG_paperC_theorems.py", "producer_sha256": sha(__file__),
           "input": INPUT, "input_sha256": sha(SRC / INPUT),
           "input_source_sha256": src["source_sha256"], "resolved_or_resampled_anything": False,
           "figure": str(FIG), "checks": CHECKS, "all_passed": True}
    with open(REC, "w") as f:
        json.dump(rec, f, indent=2)
    print(f"wrote {FIG}, {REC}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
