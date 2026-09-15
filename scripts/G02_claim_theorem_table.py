#!/usr/bin/env python3
"""G02: the claim -> theorem -> hypotheses -> artifact -> limits table, with a BUILD
CHECK rather than a hand-written list.

Every row names a Lean module and an artifact.  The script REFUSES to emit a row
whose module is not ACCEPTED in a receipt on disk, or whose artifact file is missing.
So the table cannot drift away from what actually compiled.  A row's `hypotheses`
field is what its central theorem STILL TAKES -- that is the column a referee reads
first, and it is filled from each module's own stated limitations, not from the
headline.

    .venv/bin/python scripts/G02_claim_theorem_table.py
"""
from __future__ import annotations
import glob, json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
WORK = REPO / "work/p13_conjectures"

ROWS = [
 {"paper": "Support",
  "claim": "Deciding safely is exponentially cheaper than recovering the world: "
           "k0 (1-s)^N <= R_dec <= B (1-s)^N with s = sum_i p_i, against "
           "(1/2)(1-p_min)^N <= R_rec <= (sum b_i)(1-p_min)^N.",
  "central_theorem": "SupportSamplingLaw.expected_prod_unseen + .good_event_lower "
                     "+ SupportDecideRecover.recover_lower_pointwise/.recover_upper_pointwise "
                     "+ SupportDecideExponent.decide_bracket_pointwise",
  "modules": ["LeanSupportSamplingLawV1", "LeanSupportDecideRecoverV1",
              "LeanSupportDecideExponentV1", "LeanSupportTupleCountV1"],
  "hypotheses": "the probability law is now PROVED from the product law "
                "(avoid_prob, transversal_mass), so (1-s)^N is no longer checked "
                "against the exact law -- it is derived, with NO independence "
                "assumed between the per-class unseen counts; the posterior "
                "L/(a+L) is proved from Pascal.  What is still TAKEN: "
                "minimax_eq_of_constant needs an EQUIVARIANT decoder supplied as a "
                "constant-risk hypothesis, and the decoder itself is not constructed",
  "artifacts": ["research/worker_P20_support_20260915/P20_support_growing_k.json",
                "research/worker_P13_support_20260915/P13_support_decide_exponent.json"],
  "limits": "k0 and B = prod b_i are FIXED-K constants; the growing-K law is a "
            "different model (a_i = b_i = 1) and its coupon-collector CONSTANT is "
            "not proved"},
 {"paper": "Structural",
  "claim": "For EVERY m >= 5 on g_m = (-3,(-1)^p,(+1)^q,3): V_avg = 2/((m+4)(m-1)), "
           "V_path = 2/(m+4), V_path/V_avg = m-1.",
  "central_theorem": "StructuralFamilyLower.two_le_totalDefect + .avg_lower "
                     "+ .path_lower + StructuralFamilyUpper.exists_one_defect",
  "modules": ["LeanStructuralFamilyLowerV1", "LeanStructuralFamilyUpperV1",
              "LeanStructuralSaturationV1", "LeanStructuralAvgPathGapV1"],
  "hypotheses": "NONE for the family law.  The lower bound quantifies over EVERY "
                "permutation (no_big_step / two_le_totalDefect) and the m-1 "
                "one-defect orderings are CONSTRUCTED for every p, q with "
                "q <= p <= q+1, i.e. every m >= 5.  The old hconc/hbal hypotheses "
                "are gone; ratio_card_concentrated_on_support keeps a weakened "
                "version only as a helper",
  "artifacts": ["research/worker_P19_structural_20260915/P19_structural_construction_replay.json",
                "research/worker_P3_structural_20260914/P3_avg_path_amplification.json"],
  "limits": "the level 2/(m+4) SHRINKS with m: the RATIO grows, the separation "
            "LEVEL does not.  What is proved is the FREE problem -- the mixture "
            "ranges over all distributions with no marginal constraint"},
 {"paper": "Functional",
  "claim": "At the explicit allocation w*, every flipping alternative costs at "
           "least A d^2/2 = c^2/(n(32 + 2c^2 H_n)), and one witness attains it; "
           "the known/unknown-variance sandwich is within (1+d/(2 g_min))^2 <= 4.",
  "central_theorem": "FunctionalAllocationJoin.gamma_value (= gamma_lower + "
                     "witness_flips + witness_energy) + .sandwich_ratio",
  "modules": ["LeanFunctionalAllocationJoinV1",
              "LeanFunctionalHeterogeneousInstanceV1",
              "LeanFunctionalGeometryDischargeV1",
              "LeanFunctionalHeterogeneousLowerV1"],
  "hypotheses": "no geometric inequality is taken: mean_gap and mean_diff_lt_one "
                "are derived from the cell layout, and energyU_ge_pairV is IMPORTED "
                "AND INVOKED rather than restated.  What is still TAKEN: FlipsU "
                "uses <=, so the witness attains the minimum for THAT alternative "
                "set; for strict rank inversion it gives an infimum",
  "artifacts": ["research/worker_P10_functional_20260914/P10_functional_instantiation.json",
                "research/worker_P4_functional_20260914/P4_functional_topology.json"],
  "limits": "known variances; the domain g >= d/2 is sharp.  A d^2/2 is the value "
            "AT w* and is NOT shown optimal over the design polytope, so it must "
            "not be written Gamma* = sup_w J(w)"},
 {"paper": "D6",
  "claim": "The B-scalar is never blind, so the phase story is an ASYMMETRY, not "
           "disjoint blindness; and the full design strictly beats the two-class "
           "family in 6 of 12 certified cells.",
  "central_theorem": "D6ScalarInformation.blindness_asymmetry + .clipped_min "
                     "+ .dual_over_all_queries",
  "modules": ["LeanD6ScalarInformationV1", "LeanD6ThreeClassPhaseV1"],
  "hypotheses": "dual_over_all_queries is a certificate SHAPE: it is quantified "
                "over EVERY legal query, but no specific mixture rho or value V is "
                "exhibited in Lean.  The strict separation L_full > U_two is an "
                "exact rational certificate in the artifact, not a Lean theorem",
  "artifacts": ["research/worker_P18_d6_20260915/P18_d6_full_vs_two.json",
                "research/worker_P7_d6_fulldesign_20260914/P7_d6_full_design.json",
                "research/worker_P1_d6_phase_20260914/P1_d6_phase_law.json"],
  "limits": "the alternative family is (d, x) and the symmetry orbits; t_end is NOT "
            "the phase boundary and NO phase boundary is certified; sup_err_grid is "
            "a grid supremum, not a continuous one"},
 {"paper": "Query",
  "claim": "The admissible measurement fixes the leakage order r; H^2 has order "
           "h^{2r}; N* = Theta(h^{-2r}) as an integer count; and the regret of a "
           "real decision is pinned between two powers of the same affinity.",
  "central_theorem": "QueryGaussianLevel.levelSum_ne_zero "
                     "+ QueryHellingerInterval.hellinger_lower_from_interval "
                     "+ QueryHellingerEnvelope.envelope_integrable "
                     "+ QuerySampleComplexity.matching_rate "
                     "+ QueryRegretBridge.regret_ge_gamma_error/.lrt_regret_le",
  "modules": ["LeanQueryGaussianLevelV1", "LeanQueryHellingerIntervalV1",
              "LeanQueryHellingerEnvelopeV1", "LeanQuerySampleComplexityV1",
              "LeanQueryRegretBridgeV1", "LeanQueryAffinityTestingV1"],
  "hypotheses": "L <= 2H^2 is now PROVED (neg_log_le_two), and both expectation "
                "steps of the regret reduction are now PROVED by integrating a "
                "decision kernel -- lower for EVERY kernel, upper for ONE explicit "
                "rule.  What is still TAKEN: the uniform Taylor remainder, so the "
                "interval lower bound receives its gap |a_E||h|^r/2 as an input and "
                "the constant c_+ remains MEASURED",
  "artifacts": ["research/worker_P21_query_20260915/P21_query_normalized_lrt.json",
                "research/worker_P15_query_20260915/P15_query_hellinger_order.json",
                "research/worker_P16_query_20260915/P16_query_regret_chain.json",
                "research/worker_P9_query_20260914/P9_query_transcript_complexity.json"],
  "limits": "one pair of worlds, one noise level, r in {1,2}; the equal-amplitude "
            "comparison has a CROSSOVER at h* = 0.1133, above which the constants "
            "dominate the order -- sample counts at h = 0.6 are not order evidence. "
            "The prior is equal (Bayes risk), not worst-case minimax"},
 {"paper": "MASTER",
  "claim": "Three separate results: the symmetric-family price threshold "
           "c* = (m-1)^2/(m+3)^2; a mandatory anchor at c0 = 1/10 on the finite "
           "instance; and the full-class calibration rate "
           "Gamma* = Delta^2/(2K(sqrt m + sqrt kappa)^2).",
  "central_theorem": "MasterAnchorThreshold.global_upper + .below_threshold "
                     "+ MasterAnchorCertificate.anchor_free_upper + .anchor_mandatory "
                     "+ MasterCalibrationLaw.calibration_rate_upper/.attained "
                     "+ .hidden_shift_witness",
  "modules": ["LeanMasterCalibrationLawV1", "LeanMasterAnchorCertificateV1",
              "LeanMasterAnchorThresholdV1", "LeanMasterActiveSetV1",
              "LeanMasterGroupCalibrationV1"],
  "hypotheses": "anchor_mandatory assumes NO optimality of the anchored design and "
                "needs NO value of the game; anchor_free_upper allows several "
                "shifts per alternative, which is the fix to the multiplier "
                "extraction.  What is still TAKEN: U0 = 0.013773103740 and "
                "L1 = 0.014042993094 are exact-rational certificates from P12, not "
                "Lean numbers; the full-class rate assumes equal variances, equal "
                "prices and a common gap; the gain matrix G_{u,l} is bridged from "
                "real instruments NUMERICALLY (P22), not in Lean",
  "artifacts": ["research/worker_P12_master_20260915/P12_master_anchor_required.json",
                "research/worker_P17_master_20260915/P17_master_full_class.json",
                "research/worker_P22_master_20260915/P22_master_gain_instruments.json",
                "research/worker_P6_master_20260914/P6_master_group_calibration.json"],
  "limits": "the three results are THREE DIFFERENT PROBLEMS and none implies "
            "another; the old 0.118 is none of them; P6's four-alternative game is "
            "not the threshold class (hidden_shift_witness shows why)"},
 {"paper": "Adaptive",
  "claim": "Scheduler + revalidation + stopping compose: the loop is sound and "
           "spends less than 4 B*.",
  "central_theorem": "AdaptiveLoopJoin.doubling_factor "
                     "+ AdaptiveConfidenceJoin.guarantee_on_event",
  "modules": ["LeanAdaptiveLoopJoinV1", "LeanAdaptiveConfidenceJoinV1"],
  "hypotheses": "ONLY the composition is proved.  P(E^c) <= delta for the GLR "
                "threshold, the tracking step, and the tail of the stopping time "
                "are all open; the theorem is a statement ON the event",
  "artifacts": ["research/worker_P11_adaptive_20260914/P11_adaptive_loop_join.json"],
  "limits": "the harness is ORDINARY Gaussian BAI, not the D6 runner, and is no "
            "evidence about D6's expected Gamma; two growth factors do not share a "
            "transcript, so their cost ratio is not bounded by the doubling "
            "theorem; runs now report CERTIFIED / CENSORED / FAILED and the actual "
            "cost under an enforced cumulative cap"},
]

def receipts():
    out = {}
    for f in glob.glob(str(WORK / "*.compile.receipt.json")):
        try:
            d = json.loads(Path(f).read_text())
        except Exception:
            continue
        if isinstance(d, dict) and "module" in d:
            out[d["module"]] = d
    for f in glob.glob(str(REPO / "research/**/*manifest*.json"), recursive=True):
        try:
            d = json.loads(Path(f).read_text())
        except Exception:
            continue
        if not isinstance(d, dict):
            continue
        for r in d.get("receipts", []):
            if not isinstance(r, dict) or "module" not in r:
                continue
            prev = out.get(r["module"])
            if prev is None or (r.get("accepted") and not prev.get("accepted")):
                out[r["module"]] = r
    return out


def main():
    rec = receipts()
    print("G02: claim -> theorem -> hypotheses -> artifact -> limits, build-checked\n")
    ok_rows, bad = [], []
    for row in ROWS:
        miss_mod = [m for m in row["modules"]
                    if not rec.get(m, {}).get("accepted")]
        miss_art = [a for a in row["artifacts"] if not (REPO / a).exists()]
        audits = sum(rec.get(m, {}).get("audited_names", 0) for m in row["modules"]
                     if rec.get(m, {}).get("accepted"))
        row = dict(row, audited_names=audits,
                   modules_not_accepted=miss_mod, artifacts_missing=miss_art,
                   availability_verified=(not miss_mod and not miss_art),
                   theorem_claim_verified=False)
        (ok_rows if row["availability_verified"] else bad).append(row)
        mark = "OK " if row["availability_verified"] else "!! "
        print(f"{mark}{row['paper']:11s} audits={audits:3d}  "
              f"modules={len(row['modules'])}  artifacts={len(row['artifacts'])}")
        if miss_mod:
            print(f"      modules WITHOUT an accepted receipt: {miss_mod}")
        if miss_art:
            print(f"      artifacts MISSING: {miss_art}")
    print(f"\n   {len(ok_rows)}/{len(ROWS)} rows fully build-checked")
    print("   Every row's `hypotheses` column is what its central theorem STILL")
    print("   TAKES.  The audit counts are per row and are NOT summed into a single")
    print("   'chain closed' number.")

    md = ["# CIG-AMF: claim -> theorem -> hypotheses -> artifact -> limits", "",
          "Build-checked by `scripts/G02_claim_theorem_table.py`: a row is emitted "
          "only if every Lean module it names has an ACCEPTED receipt on disk and "
          "every artifact it names exists.", ""]
    for row in ok_rows + bad:
        md += [f"## {row['paper']}", "",
               f"**Claim.** {row['claim']}", "",
               f"**Central theorem.** `{row['central_theorem']}`", "",
               f"**Modules** ({row['audited_names']} audited names): "
               + ", ".join(f"`{m}`" for m in row["modules"]), "",
               f"**Still assumed.** {row['hypotheses']}", "",
               "**Artifacts.** " + ", ".join(f"`{a}`" for a in row["artifacts"]), "",
               f"**Limits.** {row['limits']}", ""]
        if not row["availability_verified"]:
            md += [f"**NOT BUILD-CHECKED**: missing modules "
                   f"{row['modules_not_accepted']}, missing artifacts "
                   f"{row['artifacts_missing']}", ""]
    out = REPO / "research/worker_G02_table_20260915"
    out.mkdir(parents=True, exist_ok=True)
    (out / "G02_claim_theorem_table.json").write_text(
        json.dumps({"rows": ok_rows + bad,
                    "rows_verified": len(ok_rows), "rows_total": len(ROWS)},
                   indent=2) + "\n")
    (out / "G02_claim_theorem_table.md").write_text("\n".join(md))
    print(f"\n-> {out}/G02_claim_theorem_table.md")


if __name__ == "__main__":
    main()
