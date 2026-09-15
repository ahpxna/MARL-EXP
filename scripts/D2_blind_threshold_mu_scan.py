#!/usr/bin/env python3
"""D6: locate the mu-boundary where the blind design changes support.

`scripts/D1_blind_allocation_threshold.py` found zeta_blind IDENTICAL at
mu = 0.25 and mu = 0.5 and lower at mu = 0.75, and the optimal blind allocation
sitting entirely on ONE class (joint width q, h = false) for mu <= 1/2 while
scalars take over at mu = 0.75. This scans mu to test whether the support change
and the zeta_blind kink are the same point.

    .venv/bin/python scripts/D2_blind_threshold_mu_scan.py
"""
import importlib.util, json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "d1", REPO / "scripts" / "D1_blind_allocation_threshold.py")
d1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(d1)


def main():
    g = d1.load_game()
    rows = []
    print(f"{'q':>3}{'mu':>8}{'Gamma':>12}{'V_blind':>12}{'zeta':>10}  support")
    for q in (3, 4):
        for mu in [0.1, 0.2, 0.3, 0.4, 0.5, 0.55, 0.6, 0.625, 0.65, 0.675,
                   0.7, 0.75, 0.8, 0.9]:
            try:
                gam, _, _, _, _ = d1.solve_value(g, q, mu, 0.0, False)
                vb, _, _, classes, m = d1.solve_value(g, q, mu, 0.0, True)
            except Exception as e:
                print(f"{q:>3}{mu:>8}  FAILED: {type(e).__name__}: {e}")
                continue
            sup = sorted((str(c), float(v)) for c, v in zip(classes, m) if v > 1e-9)
            zeta = 1 - vb / gam
            rows.append({"q": q, "mu": mu, "Gamma": gam, "V_blind": vb,
                         "zeta_blind": zeta,
                         "support": [c for c, _ in sup],
                         "support_mass": {c: v for c, v in sup}})
            print(f"{q:>3}{mu:>8}{gam:>12.7f}{vb:>12.7f}{zeta:>10.6f}  "
                  + "  ".join(c for c, _ in sup))
    # where does the support change, and where does zeta stop being constant?
    print("\nboundaries:")
    for q in (3, 4):
        rs = [r for r in rows if r["q"] == q]
        chg = [(a["mu"], b["mu"]) for a, b in zip(rs, rs[1:])
               if a["support"] != b["support"]]
        kink = [(a["mu"], b["mu"]) for a, b in zip(rs, rs[1:])
                if abs(a["zeta_blind"] - b["zeta_blind"]) > 1e-9]
        print(f"  q={q}: support changes in {chg}")
        print(f"        zeta_blind changes in {kink}")
    out = REPO / "research/worker_D_blind_20260914/D2_blind_threshold_mu_scan.json"
    out.write_text(json.dumps({
        "question": "does the blind design's support change at the same mu where "
                    "zeta_blind stops being constant?",
        "epsilon": 0.0, "answer_shell": 0, "rows": rows,
        "scope": "floating-point LP, duality gap below 2e-8; q in {3,4}; a grid in "
                 "mu, not a proof of where the boundary is.",
    }, indent=2) + "\n")
    print(f"-> {out}")


if __name__ == "__main__":
    main()
