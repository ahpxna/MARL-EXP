#!/usr/bin/env python3
"""Query, high-risk direction 11 ("rui ro empirical cao"): read the restricted-decoder
artifact and state what it actually supports.

`scripts/QUERY_restricted_decoder_exact.py` runs the supervisor's six steps and builds
its own falsifiability guards. It does NOT print a verdict. This script reads the
artifact and applies the two guards the package itself declares, because a repair that
passes step 6 numerically can still be worthless:

  GUARD 1 (degeneracy). A bad pair is DEGENERATE when the shared restricted summary is
  the all-zero effect profile. A result carried only by degenerate pairs says nothing
  more than "a 1-step query sees nothing", which is not a repair theorem.

  GUARD 2 (memorisation). A purchased catalog that removes every bad pair by making
  nearly every fibre a singleton is a lookup table, not a decoder. The tell is the
  singleton unit fraction together with the holdout abstention rate.

    .venv/bin/python scripts/H11_repair_verdict.py
"""
from __future__ import annotations

import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
ART = REPO / "research/worker_H11_query_20260914/QUERY_restricted_decoder.json"


def main():
    d = json.loads(ART.read_text())
    acc = d["accounting"]
    base = d["catalog_purchases"][0]
    full = d["repair"]["full_catalog_result"]
    print("Direction 11: minimal repair on reachable states -- what the panel supports\n")
    print("ACCOUNTING (step 2), and it closes")
    print(f"   {acc['generated_env_steps_in_collection']} env steps -> "
          f"{acc['reachable_snapshots']} reachable snapshots -> "
          f"{acc['units_total']} units")
    print(f"   constant target (all-zero): {acc['units_constant_target_cT_all_zero']}"
          f"   evaluable non-constant: {acc['units_evaluable_nonconstant_target']}")
    print(f"   accounting_closes = {acc['accounting_closes']}; determinism violations "
          f"= {d['determinism_check']['violations']}; RNG-only target variation groups "
          f"= {d['stochastic_floor_check']['groups_where_target_varies_with_rng_only']}")

    print("\nSTEP 3-4, before buying anything")
    print(f"   bad pairs with distinct physical state : "
          f"{base['bad_pairs_distinct_physical_state']}")
    print(f"   of which NONDEGENERATE                 : "
          f"{base['bad_pairs_nondegenerate_summary']}")
    print(f"   restricted decoder: {base['n_fibres']} fibres, minimax worst-case "
          f"|error| {base['minimax_worst_case_abs_error']}, variance explained "
          f"{base['variance_explained_float']:.6f}")

    print("\nSTEP 5-6, the repair")
    print(f"   minimum catalog items reaching zero bad pairs: "
          f"{d['repair']['minimum_items_to_zero_bad_pairs']}")
    print(f"   cheapest such subsets: "
          f"{d['repair']['subsets_reaching_zero_bad_pairs'][0]}")
    print(f"   full catalog: bad pairs {full['bad_pairs_distinct_physical_state']}, "
          f"variance explained {full['variance_explained_float']:.3f}, "
          f"{full['n_fibres']} fibres")
    print(f"   singleton unit fraction {full['singleton_unit_fraction_float']:.4f}"
          f"   holdout abstention {full['holdout']['abstain_rate_float']:.4f}"
          f" ({full['holdout']['abstained_unseen_summary']} of "
          f"{full['holdout']['test_units']} test units)")

    g1 = base["bad_pairs_nondegenerate_summary"] > 0
    g2 = (full["singleton_unit_fraction_float"] < 0.5
          and full["holdout"]["abstain_rate_float"] < 0.5)
    print("\nGUARDS")
    print(f"   GUARD 1, nondegenerate bad pairs exist : {'PASS' if g1 else 'FAIL'}")
    print(f"   GUARD 2, the repair is not memorisation: {'PASS' if g2 else 'FAIL'}")

    print("\nVERDICT")
    if g1 and g2:
        print("   Both guards pass: the repair is a genuine one on this panel.")
    else:
        print("   The package RUNS and its accounting closes, but the result it")
        print("   supports is WEAK, and the package's own guards are what say so:")
        if not g1:
            print("   - every bad pair is DEGENERATE: the shared restricted summary is")
            print("     the all-zero effect profile, so the finding reduces to 'a")
            print("     1-step query sees nothing'. That is not a repair theorem.")
        if not g2:
            print(f"   - the repair reaches zero bad pairs by memorising: "
                  f"{100*full['singleton_unit_fraction_float']:.1f}% of units end in")
            print(f"     singleton fibres and the decoder abstains on "
                  f"{100*full['holdout']['abstain_rate_float']:.1f}% of held-out units.")
            print("     Variance explained 1.0 on the training panel is a lookup table,")
            print("     not generalisation.")
        print("   Per the supervisor's own framing this is the empirical risk of the")
        print("   direction MATERIALISING, not a reason to keep buying features. What")
        print("   the direction needs first is a panel with nondegenerate bad pairs --")
        print("   i.e. reachable states whose 1-step effect profiles genuinely agree")
        print("   while their horizon-6 targets differ -- and this panel has none.")

    out = REPO / "research/worker_H11_query_20260914/H11_repair_verdict.json"
    out.write_text(json.dumps({
        "source_artifact": str(ART.relative_to(REPO)),
        "accounting_closes": acc["accounting_closes"],
        "bad_pairs_total": base["bad_pairs_distinct_physical_state"],
        "bad_pairs_nondegenerate": base["bad_pairs_nondegenerate_summary"],
        "min_items_to_zero_bad_pairs": d["repair"]["minimum_items_to_zero_bad_pairs"],
        "full_catalog_singleton_fraction": full["singleton_unit_fraction_float"],
        "holdout_abstain_rate": full["holdout"]["abstain_rate_float"],
        "guard_nondegenerate_pairs": g1,
        "guard_not_memorisation": g2,
        "verdict": ("genuine repair" if g1 and g2 else
                    "WEAK: all bad pairs degenerate and/or the repair is memorisation"),
        "not_established": [
            "one RWARE panel, one fixed collection policy, 20 episodes",
            "no theorem; this is an empirical probe and its guards are what decide it",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
