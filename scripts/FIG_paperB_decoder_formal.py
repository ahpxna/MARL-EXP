#!/usr/bin/env python3
"""Paper B, figure B-F6': the decoder panel drawn from the FORMALIZED decoder's own counts.

Why this exists (audit 2026-09-24).  `FIG_new_panels.py` draws `paperB_decoder.pdf` from the
script rule's counts (`paperB_decoder_grid_v2_20260923.json`).  For the identification task the
script rule counts an ambiguous outcome as an error, while the formalized decoder (`idCode`,
`decodeB`) answers a default world there.  `lean_wrong_imp_py_wrong` makes the script's counts an
UPPER bound on the formalized decoder's errors.  So the script's upper certificates are
conservative for the formalized decoder, but its LOWER brackets are not: a lower confidence bound
on the script rule's error does not bound the formalized decoder's error from below.  Both
bounds must come from the formalized decoder's own counts.  These are in
`paperB_decoder_leanfallback.json`: the paired rerun with the formalized fallback, same seed and
draws, 10/10 checks.  Nothing is resampled here.

Panels: (1) safe decoder, (2) identification decoder, family-wise Clopper-Pearson upper (solid)
and lower (dotted) worst-world error against the total budget, m = 3; (3) the closed-form order
slopes (unchanged, from `paperB_decoder.json`).

SELF-CHECKS (refuse to draw):
  * the input passed its checks and names its producer and its pairing;
  * the certificates and failed prefixes recomputed here from the rows reproduce the input's
    `certified` field exactly (a transcription or rule error would fail);
  * every safe count equals the script's (pairing) and every identification count is at most the
    script's (`lean_wrong_imp_py_wrong` on data);
  * the bracket comparison with the script rule is recorded, not assumed.

Outputs (new files; refuse to overwrite):
    research/papers/_figures/paperB_decoder_formal.pdf
    research/unified_20260919/paperB_decoder_formal_figure.json
"""

import hashlib
import json
import pathlib
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

SRC = pathlib.Path("research/unified_20260919")
FIG = pathlib.Path("research/papers/_figures/paperB_decoder_formal.pdf")
REC = SRC / "paperB_decoder_formal_figure.json"
LEAN = "paperB_decoder_leanfallback.json"
SCRIPT = "paperB_decoder.json"
GRIDV2 = "paperB_decoder_grid_v2_20260923.json"
plt.rcParams.update({"font.size": 7, "axes.linewidth": 0.6})
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def panels(rows, delta):
    """Worst-world family-wise bounds per (m, h, decoder, N), and the certificate rule."""
    by = {}
    for r in rows:
        k = (r["m"], r["h"], r["decoder"])
        e = by.setdefault(k, {}).setdefault(r["N_per_query"], {"up": 0.0, "lo": 0.0,
                                                               "total": r["total_budget"]})
        e["up"] = max(e["up"], r["err_upper_fw"])
        e["lo"] = max(e["lo"], r["err_lower_fw"])
    out = {}
    for k, grid in by.items():
        Ns = sorted(grid)
        cert = next((N for N in Ns if grid[N]["up"] <= delta), None)
        prefix = []
        for N in Ns:
            if grid[N]["lo"] > delta:
                prefix.append(N)
            else:
                break
        lower_incl = Ns[len(prefix)] if len(prefix) < len(Ns) else None
        out[k] = {"grid": grid, "certified_N": cert, "failed_prefix": prefix,
                  "grid_min_lower_inclusive": lower_incl}
    return out


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
    L = json.load(open(SRC / LEAN))
    S = json.load(open(SRC / SCRIPT))
    delta = L["delta_target"]
    check("the input passed its checks and records its producer and pairing",
          L["all_passed"] and "leanfallback" in L["producer"] and bool(L.get("pairing")))
    P = panels(L["results"], delta)
    stored = {(c["m"], c["h"], c["decoder"]): c for c in L["certified"]}
    mism = [k for k, c in stored.items()
            if (P[k]["certified_N"], P[k]["failed_prefix"], P[k]["grid_min_lower_inclusive"])
            != (c["certified_N"], c["failed_prefix"], c.get("grid_min_lower_inclusive"))]
    check("certificates and failed prefixes recomputed from rows reproduce the input exactly",
          not mism and all(k in P for k in stored),
          f"{len(stored)} stored panels of {len(P)}, mismatches {mism}")
    key = lambda r: (r["decoder"], r["m"], r["h"], r["world"], r["N_per_query"])
    sc = {key(r): r["bad"] for r in S["results"]}
    safe_eq = all(sc[key(r)] == r["bad"] for r in L["results"] if r["decoder"] == "safe")
    id_le = all(r["bad"] <= sc[key(r)] for r in L["results"] if r["decoder"] != "safe")
    check("pairing: every safe count equals the script's; every identification count is at most it",
          safe_eq and id_le)
    # bracket comparison with the script rule's CORRECTED panels (grid v2, 0.05/(2J) per tail)
    V = json.load(open(SRC / GRIDV2))
    moved = []
    for q in V["panels"]:
        k = (q["m"], q["h"], q["decoder"])
        a = P.get(k)
        if a is None:
            continue
        if (a["failed_prefix"], a["certified_N"]) != (q["failed_prefix"], q["certified_upper"]):
            moved.append({"panel": list(k), "formal": [a["certified_N"], a["failed_prefix"]],
                          "script": [q["certified_upper"], q["failed_prefix"]]})
    check("the comparison with the script rule's corrected brackets was computed",
          len(V["panels"]) == len(P), f"{len(moved)} of {len(P)} panels differ")
    if not all(c["ok"] for c in CHECKS):
        print("REFUSING to draw.", file=sys.stderr)
        return 1

    fig, axes = plt.subplots(1, 3, figsize=(7.2, 2.4))
    m0 = 3
    hs = sorted({k[1] for k in P if k[0] == m0}, reverse=True)
    cmap = plt.get_cmap("viridis")
    for ax, dec, mk in ((axes[0], "safe", "o"), (axes[1], "identification", "s")):
        for i, h in enumerate(hs):
            k = (m0, h, dec)
            if k not in P:
                continue
            g = P[k]["grid"]
            Ns = sorted(g)
            xs = [g[N]["total"] for N in Ns]
            col = cmap(i / max(1, len(hs) - 1))
            ax.plot(xs, [g[N]["up"] for N in Ns], mk + "-", ms=2.5, lw=0.9, color=col,
                    label=f"h={h}")
            ax.plot(xs, [max(g[N]["lo"], 1e-4) for N in Ns], lw=0.6, ls=":", color=col)
        ax.axhline(delta, color="black", lw=0.6, ls="--")
        ax.set_xscale("log"); ax.set_yscale("log"); ax.set_ylim(1e-4, 1)
        ax.set_xlabel("total budget")
        ax.set_title(f"{dec} decoder (formalized), m={m0}", fontsize=7.2)
        ax.legend(fontsize=5, frameon=False)
    axes[0].set_ylabel("worst-world error, family-wise CP")
    ax = axes[2]
    for row in S["order_rows"]:
        j = row["j"]
        ax.plot([0, 1], [row["slope_coarse_grid"], row["slope_fine_grid"]], "o-", ms=3, lw=1.0,
                label=f"j={j}")
        ax.axhline(j, color="#999", lw=0.5, ls=":")
    ax.set_xticks([0, 1]); ax.set_xticklabels(["coarse h", "fine h"])
    ax.set_ylabel("log-log slope of the mean gap")
    ax.set_title("the order converges to $j$ (exact)", fontsize=7.2)
    ax.legend(fontsize=5, frameon=False)
    fig.tight_layout()
    fig.savefig(FIG)
    plt.close(fig)
    rec = {"producer": "scripts/FIG_paperB_decoder_formal.py", "producer_sha256": sha(__file__),
           "inputs": {LEAN: sha(SRC / LEAN), SCRIPT: sha(SRC / SCRIPT), GRIDV2: sha(SRC / GRIDV2)},
           "resolved_or_resampled_anything": False, "figure": str(FIG),
           "panels_formal": [{"m": k[0], "h": k[1], "decoder": k[2],
                              "certified_N": v["certified_N"], "failed_prefix": v["failed_prefix"],
                              "grid_min_lower_inclusive": v["grid_min_lower_inclusive"]}
                             for k, v in sorted(P.items())],
           "brackets_that_differ_from_script_rule": moved,
           "checks": CHECKS, "all_passed": True}
    REC.write_text(json.dumps(rec, indent=2))
    print(f"wrote {FIG}, {REC}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
