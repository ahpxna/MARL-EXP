#!/usr/bin/env python3
"""Assemble the raw-fibre denominator-ladder saturation series and its figure.

Reads every RAWsweep_m6_d*_s*.json in the D6 falsification ledger (the _bad_args
quarantine is excluded by construction: only top-level files are globbed) and
records, per seed, the exact snapped ratio as a function of the lambda-grid
denominator together with the float lead the optimizer found.  The float lead is
denominator-independent; the exact ratio is the certificate the lead can be
snapped onto, so the series measures certification resolution, not geometry.
"""
from __future__ import annotations
import glob, json, re, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from research_chains.provenance import write_artifact_with_provenance  # noqa: E402

PROTOCOL_VERSION = "d6_raw_fiber_denominator_saturation_series_v1"
EVIDENCE_CLASS = "NUMERICAL_LEAD_WITH_EXACT_RATIONAL_RECHECK"
DIR = ROOT / "research/d6_contrast_rank_falsification"
OUT = ROOT / "research/d6_raw_contrast_rank/RAW_SATURATION_SERIES_20260906.json"
FIG = ROOT / "research/reports_append_only/figures/fig_raw_saturation_20260906.png"

t0 = time.time()
series = {}
for f in sorted(glob.glob(str(DIR / "RAWsweep_m6_d*_s*.json"))):
    if f.endswith(".manifest.json"):
        continue
    mm = re.search(r"d(\d+)_s(\d+)\.json$", f)
    if not mm:
        continue
    den, seed = int(mm.group(1)), int(mm.group(2))
    d = json.load(open(f))
    series.setdefault(seed, {})[den] = {
        "denominator": den,
        "status": d["status"],
        "exact_ratio": d["best_exact_ratio"],
        "exact_ratio_float": d["best_exact_ratio_float"],
        "float_lead": d["best_float_ratio"],
        "strict_top_c_exact_ratio": d.get("best_strict_top_c_exact_ratio"),
        "wall_clock_seconds": d.get("wall_clock_seconds"),
        "artifact": Path(f).name,
    }

seeds = sorted(series)
rows = {str(s): [series[s][d] for d in sorted(series[s])] for s in seeds}
killed = [(s, r) for s in seeds for r in rows[str(s)] if r["status"] == "KILLED"]
leads = {str(s): sorted({r["float_lead"] for r in rows[str(s)]}) for s in seeds}

result = {
    "protocol_version": PROTOCOL_VERSION,
    "development_only": True,
    "evidence_class": EVIDENCE_CLASS,
    "m": 6, "alphabet": 3, "reference": "corners", "fiber_kind": "raw",
    "snap": "coefficients", "min_topc_margin": 0.02, "optimizer": "de+both+lp",
    "runs_total": sum(len(v) for v in rows.values()),
    "seeds": seeds,
    "series_by_seed": rows,
    "float_leads_by_seed": leads,
    "killed_runs": [{"seed": s, **r} for s, r in killed],
    "max_exact_ratio_overall": max(r["exact_ratio_float"] for s in seeds for r in rows[str(s)]),
    "max_float_lead_overall": max(r["float_lead"] for s in seeds for r in rows[str(s)]),
    "readings": [
        "The float lead is constant in the denominator for every seed except 13 "
        "(0.9602557582657572 at d4-d32, 0.9634775563081881 at d64): the optimizer stack is "
        "seeded identically and the lambda grid does not change the float search, only which "
        "rationals the lead can be snapped onto.",
        "Seed 5 is the ONLY seed whose float lead exceeds 1 (1.001451519478135), and it did "
        "so already at denominator 4. Denominators 8, 16, 32 and 64 did not find new geometry; "
        "they raised the resolution of the exact certificate until the lead could be certified. "
        "The kill was therefore visible in the first seed-5 run and took five denominators to "
        "become admissible evidence.",
        "Convergence of the exact ratio to the float lead is NOT monotone in general: seed 1 "
        "falls from 0.8928950 (d32) to 0.8920101 (d64), and seed 13 falls from 0.9561767 (d16) "
        "to 0.9527880 (d32) before returning to 0.9561767 (d64). Each denominator is an "
        "independent snapping attempt, not a refining limit. Seed 5 happens to be monotone.",
        "Nine of the ten seeds saturate strictly below 1 at their own ceiling; the ceilings are "
        "per-cell and range from 0.744 (seed 21) to 0.956 (seed 13). There is no universal raw "
        "ceiling near 0.89, which is what the seed 1-2 pair suggested in addendum B Section 95.",
        "Addendum B Section 98.4 is settled: clean seed-13 runs with --snap coefficients reach "
        "0.9561767406098319 at d16 and d64 and 0.9527879513477887 at d32, all below the "
        "0.9585 obtained with --snap both. The projection branch of the snapper did add "
        "roughly 0.0023 over every clean seed-13 value, so the original demotion reason was "
        "correct in direction; the magnitude first attributed to it (the gap to 0.8903) was "
        "not, because that gap is seed variation.",
    ],
    "wall_clock_seconds": round(time.time() - t0, 3),
}

if OUT.exists():
    # Append-only ledger: an existing artifact is never rewritten.  Re-running is
    # still useful for regenerating the figure, so this is a note, not a failure.
    print(f"note: ledger artifact already present, not rewritten: {OUT}")
else:
    OUT.parent.mkdir(parents=True, exist_ok=True)
    write_artifact_with_provenance(
        OUT, result,
        protocol={"protocol_version": PROTOCOL_VERSION, "source_glob": "RAWsweep_m6_d*_s*.json",
                  "m": 6, "alphabet": 3, "fiber_kind": "raw"},
        seed=None, evidence_class=EVIDENCE_CLASS, chain="D6")

# ---------------------------------------------------------------- figure ----
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

plt.rcParams.update({"font.size": 7.0, "axes.linewidth": 0.6,
                     "xtick.major.width": 0.6, "ytick.major.width": 0.6,
                     "font.family": "DejaVu Sans"})
fig, (axA, axB) = plt.subplots(2, 1, figsize=(3.35, 4.05),
                               gridspec_kw={"height_ratios": [1.35, 1.0], "hspace": 0.46})

GREY, HL = "#9aa3ad", "#c1272d"

# label placement: curves ending at the same denominator would collide, so the
# labels are pushed apart to a minimum vertical separation in data coordinates.
ends = {}
for s_ in seeds:
    if s_ == 5:
        continue
    r = rows[str(s_)]
    ends.setdefault(r[-1]["denominator"], []).append((r[-1]["exact_ratio_float"], s_))
label_at = {}
for xend, group in ends.items():
    group.sort()
    ys_ = [g[0] for g in group]
    gap = 0.028
    for idx in range(1, len(ys_)):
        if ys_[idx] - ys_[idx - 1] < gap:
            ys_[idx] = ys_[idx - 1] + gap
    for (y0, s_), ynew in zip(group, ys_):
        label_at[s_] = (xend, y0, ynew)

for s_ in seeds:
    if s_ == 5:
        continue
    r = rows[str(s_)]
    xs = [x["denominator"] for x in r]
    ys = [x["exact_ratio_float"] for x in r]
    axA.plot(xs, ys, marker="o", ms=2.2, lw=0.75, color=GREY, zorder=2)
    xend, y0, ylab = label_at[s_]
    axA.annotate(f"{s_}", (xend, y0), xytext=(xend * 1.16, ylab),
                 textcoords="data", fontsize=5.4, color="#6b7480", va="center",
                 arrowprops=dict(arrowstyle="-", lw=0.35, color="#c3c9d0",
                                 shrinkA=0.5, shrinkB=1.0))
xs = [r["denominator"] for r in rows["5"]]
ys = [r["exact_ratio_float"] for r in rows["5"]]
axA.plot(xs, ys, marker="o", ms=3.4, lw=1.6, color=HL, zorder=4)
axA.axhline(1.0, color="#1a1a1a", lw=0.9, ls=(0, (4, 2)), zorder=3)
axA.plot([64], [ys[-1]], marker="*", ms=9.5, color=HL, zorder=5,
         markeredgecolor="white", markeredgewidth=0.5)
axA.annotate("seed 5", (4, ys[0]), xytext=(3, -8.5), textcoords="offset points",
             fontsize=6.0, color=HL, fontweight="bold")
axA.annotate("KILLED  1.000440", (64, ys[-1]), xytext=(-2, 8),
             textcoords="offset points", fontsize=6.0, color=HL, ha="right",
             fontweight="bold")
axA.annotate("2D = (m\u22121)\u00b7\u03b4\u25a1", (4.15, 1.0), xytext=(0, 3.5),
             textcoords="offset points", fontsize=5.8, color="#1a1a1a")
axA.set_xscale("log", base=2)
axA.set_xticks([4, 8, 16, 32, 64]); axA.set_xticklabels(["4", "8", "16", "32", "64"])
axA.set_xlim(3.5, 108); axA.set_ylim(0.58, 1.052)
axA.set_xlabel("\u03bb-grid denominator", labelpad=1.5)
axA.set_ylabel("exact snapped  2D / ((m\u22121)\u00b7\u03b4\u25a1)", labelpad=2)
axA.set_title("A   Raw fibre: exact certificate vs snapping resolution",
              fontsize=7.2, loc="left", pad=5)
for sp in ("top", "right"):
    axA.spines[sp].set_visible(False)

order = sorted(seeds, key=lambda s_: leads[str(s_)][-1])
y = list(range(len(order)))
axB.hlines(y, [min(r["exact_ratio_float"] for r in rows[str(s_)]) for s_ in order],
           [leads[str(s_)][-1] for s_ in order], color="#dde1e6", lw=2.4, zorder=1)
axB.scatter([max(r["exact_ratio_float"] for r in rows[str(s_)]) for s_ in order], y,
            s=12, color=["#c1272d" if s_ == 5 else "#3d4653" for s_ in order], zorder=4)
axB.scatter([leads[str(s_)][-1] for s_ in order], y, s=15, facecolors="white",
            edgecolors=["#c1272d" if s_ == 5 else "#8b949e" for s_ in order], lw=0.9,
            zorder=3)
axB.axvline(1.0, color="#1a1a1a", lw=0.9, ls=(0, (4, 2)), zorder=2)
axB.set_yticks(y); axB.set_yticklabels([f"seed {s_}" for s_ in order], fontsize=6.0)
axB.set_xlim(0.58, 1.055); axB.set_ylim(-0.7, len(order) - 0.3)
axB.set_xlabel("ratio  2D / ((m\u22121)\u00b7\u03b4\u25a1)", labelpad=1.5)
axB.set_title("B   Only seed 5 has a float lead above the bound",
              fontsize=7.2, loc="left", pad=5)
from matplotlib.lines import Line2D
axB.legend(handles=[
    Line2D([], [], marker="o", ls="none", ms=3.4, color="#3d4653",
           label="best exact certificate"),
    Line2D([], [], marker="o", ls="none", ms=3.8, markerfacecolor="white",
           markeredgecolor="#8b949e", color="#8b949e", label="float lead (uncertified)")],
    fontsize=5.6, frameon=False, loc="upper left", handletextpad=0.35,
    borderaxespad=0.3, labelspacing=0.3)
for sp in ("top", "right"):
    axB.spines[sp].set_visible(False)

FIG.parent.mkdir(parents=True, exist_ok=True)
fig.savefig(FIG, dpi=340, bbox_inches="tight", facecolor="white")
print(json.dumps({"artifact": str(OUT), "figure": str(FIG),
                  "runs": result["runs_total"], "seeds": seeds,
                  "killed": [(s, r["denominator"]) for s, r in killed],
                  "max_exact": result["max_exact_ratio_overall"],
                  "max_float": result["max_float_lead_overall"]}, indent=2))
