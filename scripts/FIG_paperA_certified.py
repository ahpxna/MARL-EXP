#!/usr/bin/env python3
"""Paper A, figure A-F1: the certified interval for Gamma_true / Gamma_proxy against r (M = 1),
from `paperA_certified_separation.json` (no resolving), inside the proved bracket.

SELF-CHECKS (refuse to draw on failure): the input passed its own self-checks; every interval
satisfies L <= U; every interval sits inside the proved bracket
`4/(4+2rM) <= ratio <= 64/(9rM)` (`centred_separation`), recomputed here from the Lean
formulas, not read from the file.

Outputs (new files; refuse to overwrite):
    research/papers/_figures/paperA_certified.pdf
    research/unified_20260919/paperA_certified_figure.json
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
FIG = pathlib.Path("research/papers/_figures/paperA_certified.pdf")
REC = SRC / "paperA_certified_figure.json"
INPUT = "paperA_certified_separation.json"
plt.rcParams.update({"font.size": 8, "axes.labelsize": 8, "axes.titlesize": 8.5,
                     "legend.fontsize": 6.2, "xtick.labelsize": 7, "ytick.labelsize": 7,
                     "figure.dpi": 200, "savefig.dpi": 200, "axes.grid": True,
                     "grid.alpha": 0.25, "grid.linewidth": 0.5})
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


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
    d = json.load(open(SRC / INPUT))
    M = d["M"]
    G = Fr(9, 512)
    rows = d["rows"]
    check("the input passed its own self-checks and names its producer",
          d["all_passed"] and d["producer"] == "scripts/EXP_paperA_certified_separation.py")
    ok_lu, ok_br, det = True, True, []
    rs, lo, up = [], [], []
    for row in rows:
        r = row["r"]
        L, U = Fr(row["Gamma_true_lower"]), Fr(row["Gamma_true_upper"])
        ok_lu &= L <= U
        blo, bup = Fr(4, 4 + 2 * r * M), Fr(64, 9 * r * M)
        ok_br &= (blo <= L / G) and (U / G <= bup)
        rs.append(r); lo.append(float(L / G)); up.append(float(U / G))
        det.append(f"r={r}: [{float(L / G):.5f}, {float(U / G):.5f}] in [{float(blo):.3f}, {float(bup):.3f}]")
    check("every certified interval has L <= U", ok_lu)
    check("every certified interval lies inside the proved bracket 4/(4+2rM) <= ratio <= 64/(9rM)",
          ok_br, "; ".join(det))
    if not all(c["ok"] for c in CHECKS):
        print("REFUSING to draw.", file=sys.stderr)
        return 1
    fig, a = plt.subplots(1, 1, figsize=(3.4, 2.5))
    rg = np.arange(1, 9)
    a.fill_between(rg, [4 / (4 + 2 * r * M) for r in rg], [64 / (9 * r * M) for r in rg],
                   color="#4C72B0", alpha=0.12, label="proved bracket")
    a.plot(rg, [4 / (4 + 2 * r * M) for r in rg], color="#4C72B0", lw=0.8)
    a.plot(rg, [64 / (9 * r * M) for r in rg], color="#4C72B0", lw=0.8)
    mid = [(l + u) / 2 for l, u in zip(lo, up)]
    a.errorbar(rs, mid, yerr=[[m - l for m, l in zip(mid, lo)], [u - m for m, u in zip(mid, up)]],
               fmt="o", color="k", ms=3.5, capsize=2,
               label="certified interval (exact rational)")
    a.axhline(1.0, color="#C44E52", ls="--", lw=0.8, label=r"$\Gamma_{\rm true}=\Gamma_{\rm proxy}$")
    a.set_xscale("log", base=2); a.set_yscale("log")
    a.set_xticks(rs); a.set_xticklabels([str(r) for r in rs])
    a.set_xlabel(r"$r$ (pairs of middle cells), $M=1$")
    a.set_ylabel(r"$\Gamma_{\rm true}/\Gamma_{\rm proxy}$")
    a.set_title("A-F1: centred separation, certified")
    a.legend(frameon=False, loc="upper right", fontsize=5.6)
    fig.tight_layout()
    fig.savefig(FIG)
    plt.close(fig)
    rec = {"producer": "scripts/FIG_paperA_certified.py", "producer_sha256": sha(__file__),
           "input": INPUT, "input_sha256": sha(SRC / INPUT),
           "input_source_sha256": d["source_sha256"], "resolved_or_resampled_anything": False,
           "figure": str(FIG), "intervals": [{"r": r, "ratio_lower": l, "ratio_upper": u}
                                            for r, l, u in zip(rs, lo, up)],
           "checks": CHECKS, "all_passed": True}
    with open(REC, "w") as f:
        json.dump(rec, f, indent=2)
    print(f"wrote {FIG}, {REC}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
