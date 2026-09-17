#!/usr/bin/env python3
"""G14 -- every audit item of 2026-09-15, and exactly what now closes it.

This is a BUILD-CHECKED table.  A row may claim a Lean module only if that module has
an ACCEPTED receipt whose recorded source hash equals the file's current hash, and may
claim an artifact only if the file exists.  Anything else is reported as OPEN.

No row asserts that a module's ENGLISH matches its statement; that judgement is the
supervisor's.  What is machine-checked here is: the module exists, it compiles with a
clean axiom audit, the hash matches, and the named artifact is present.
"""
import hashlib, json, os, sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
WORK = REPO / "work/p13_conjectures"
OUT = REPO / "research/worker_G14_status_20260915"


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 16), b""):
            h.update(b)
    return h.hexdigest()


def module_ok(m):
    src = WORK / f"{m}.lean"
    rec = WORK / f"{m}.compile.receipt.json"
    if not src.exists():
        return False, "source missing", 0
    if not rec.exists():
        return False, "no receipt", 0
    d = json.loads(rec.read_text())
    if not isinstance(d, dict):
        return False, "receipt is not an object", 0
    n = len(d.get("axioms", {}))
    if not d.get("accepted"):
        return False, f"receipt accepted=False (exit {d.get('lean_exit')})", n
    if d.get("source_sha256_before") != sha(src):
        return False, "source changed since the receipt", n
    return True, "accepted", n


ITEMS = [
    # id, paper, what the audit said, modules, artifacts, status_if_all_present
    ("M1", "MASTER",
     "P6's four alternatives are not the threshold class; a group shift paid back by "
     "the offset changes the answer with every ordinary mean fixed",
     ["LeanMasterCalibrationLawV1"],
     ["research/worker_P17_master_20260915/P17_master_full_class.json"],
     "CLOSED: witness certified in exact rationals; full-class rate "
     "Delta^2/(2K(sqrt m+sqrt kappa)^2) proved and confirmed numerically"),
    ("M2", "MASTER",
     "support-in-active-set is not optimality; existence of a design with M=0 does not "
     "remove the anchor",
     ["LeanMasterAnchorCertificateV1"],
     [],
     "CLOSED: the argument is now two separated certificates, sup_{x0=0} J <= U0 < L1, "
     "with no optimality of any cut assumed"),
    ("M3", "MASTER",
     "G04 wrote sup_{x0=0} J = U0 where the certificate gives only <=",
     [],
     ["research/worker_G03_G13_20260915/G04_headline_proofs.md"],
     "CLOSED: G04 now reads sup_{x0=0} J <= U0 < L1 and says so explicitly"),
    ("M4", "MASTER",
     "value_improves_iff is an equivalence over ALL alternatives, not a derivative law "
     "on the active set",
     ["LeanMasterGainFactorizationV1"],
     [],
     "CLOSED: min_attained_on_active is the quantitative replacement -- with slack s "
     "and travel Kt, 2Kt < s keeps the minimum inside the active set; inactive_dropped "
     "then licenses dropping the rest"),

    ("D1", "D6",
     "the B-scalar is not blind at x=0, so 'two disjoint blind directions' is false",
     ["LeanD6ScalarInformationV1"],
     [],
     "CLOSED: I_B(1,0)=1/96 certified, I_B > 0 for every x, and the retraction is "
     "stated as an asymmetry"),
    ("D2", "D6",
     "P7 compared L_full with L_two -- both LOWER bounds",
     [],
     ["research/worker_P18_d6_20260915/P18_d6_full_vs_two.json"],
     "CLOSED: U_two is now a dual certificate for every two-class design; L_full > "
     "U_two is STRICT in 6 of 12 cells and absent in the other 6, which is reported"),
    ("D3", "D6",
     "information is quadratic in x; checking x=0,1 does not pin it",
     [],
     ["research/worker_P18_d6_20260915/P18_d6_full_vs_two.json"],
     "CLOSED: coefficients extracted from {0,1,-1} verified at three further points, "
     "7092 exact checks"),
    ("D4", "D6",
     "cuts can outnumber the LP's multipliers if the round limit is hit",
     [],
     ["research/worker_P18_d6_20260915/P18_d6_full_vs_two.json"],
     "CLOSED: multipliers are read only from the SOLVED LP's cuts; a convergence flag "
     "is recorded per cell"),
    ("D5", "D6",
     "sup_err_grid is not a continuous supremum; a sign change on a grid does not give "
     "a boundary",
     ["LeanD6AlternativeReductionV1"],
     ["research/worker_P24_d6_corrected_20260915/P24_d6_boundary_modulus_v2.json"],
     "CLOSED for the separation claim, with the right-endpoint test CORRECTED: the left "
     "test uses rho_two = 2^((t1-t0)/q) for Gamma_two; the right test must use the "
     "widest query in the FULL primal support (reusing rho_two there was invalid).  "
     "Both verdicts now use outward RATIONAL enclosures and exact gaps, not floats.  "
     "8/8 cells certified, all of them by the left test.  A phase BOUNDARY is still not "
     "certified"),
    ("D6", "D6",
     "'whole design' is still over the (d,x) family and the symmetry orbits",
     ["LeanD6ScalarInformationV1", "LeanD6AlternativeReductionV1"],
     [],
     "CLOSED: the (d,x) parameterisation is no longer a restriction. LeanD6GeneralFamilyV1 "
     "defines the general alternative as an arbitrary shift vector, IB_eq_of_slice shows the "
     "(d,x) formula IS that information on the slice, and IB_le_general proves EVERY "
     "alternative in the class costs at least the slice value -- so a lower bound quantified "
     "over the slice is one over the class. slice_is_tight shows the bound is attained exactly "
     "on the slice"),

    ("F1", "Functional",
     "instantiated_value is only an arithmetic identity: no cell type, no allocation, "
     "no quantifier over alternatives",
     ["LeanFunctionalAllocationJoinV1"],
     [],
     "CLOSED: explicit cell type, budget, positivity, resistance identity, every "
     "ordered pair, and gamma_lower for EVERY flipping alternative"),
    ("F2", "Functional",
     "the geometry discharge is not applied to a named allocation, and no flipping "
     "alternative attains the bound",
     ["LeanFunctionalAllocationJoinV1"],
     [],
     "CLOSED: energyU_ge_pairV is invoked, and witness_flips/witness_energy give an "
     "alternative that flips and costs exactly A d^2/2"),
    ("F3", "Functional",
     "the sandwich ratio tends to 1 only when d/g_min -> 0, not merely when d -> 0",
     ["LeanFunctionalAllocationJoinV1"],
     [],
     "CLOSED: Splus_lower and sandwich_ratio give the factor (1+d/(2 g_min))^2 <= 4 on "
     "the whole domain"),
    ("F4", "Functional",
     "cells_of uses isqrt(n) without asserting n is a perfect square",
     [],
     ["scripts/P10_functional_instantiation.py",
      "scripts/F2_heterogeneous_crossover_check.py"],
     "CLOSED: both call sites now assert r*r == n"),
    ("F5", "Functional",
     "P4's Top-1 / (argmax,argmin) task is not the group-range problem",
     ["LeanFunctionalRangeAlternativeUnionV1"], [],
     "PARTIAL, with the oracle and the inner problem now CLOSED. "
     "LeanFunctionalRangeEnergyOracleV1 makes the oracle a FINITE check "
     "(energy_lower_bound_iff) and solves the inner problem exactly (inner_qp_lower, "
     "inner_qp_attained). LeanFunctionalShrinkExpandV1 proves shrink and expand as "
     "EQUIVALENCES with the clamp as the projection. LeanFunctionalRangeDesignCertificateV1 "
     "gives a KKT certificate needing NO matrix inverse, so a singular information matrix "
     "needs no pseudoinverse, plus weak duality and the direction discipline. "
     "LeanFunctionalScalarProxyFailsV1 proves the scalar proxy is a bound in NEITHER direction "
     "and by no constant. STILL OPEN: assembling the full oracle equality, which needs the "
     "model's separability across relation blocks"),
    ("F6", "Functional",
     "the physical-contrast comparison assumes the raw scalar reads are discarded",
     [],
     ["research/worker_P26_functional_corrected_20260915/P26_functional_contrast_cost_v2.json"],
     "CLOSED for the two-cell identity. LeanFunctionalDesignDualityV1.scalar_split_optimal "
     "computes the best two-cell scalar allocation exactly as (sigma_a+sigma_b)^2, "
     "breakeven_iff gives the exact break-even condition c_c*nu_c = (sigma_a+sigma_b)^2, and "
     "breakeven_not_four keeps the folklore 4 inside its hypotheses -- it is that value only "
     "at unit variances. infeasible_iff and value_of_feasible make an infeasible setup carry "
     "NO value rather than a clamped one. The multi-alternative threshold is NOT claimed and "
     "does not transfer"),
    ("F7", "Functional",
     "C_lucb beats C_anytime; the oracle variant is not a performance ceiling",
     [],
     ["research/confirm_ieee_20260912/functional_v4_lucb_ieee10seed_cellv1.json"],
     "CLOSED as a reporting rule: the panel is reported with C_lucb as the winner and "
     "the oracle variant labelled a diagnostic"),

    ("Q1", "Query",
     "RateAssembly only passes inequalities through; no N*, no log/exp, no Nat.ceil",
     ["LeanQuerySampleComplexityV1"],
     [],
     "CLOSED: log sandwich H^2 <= L <= 2H^2, the exponential inversion, and the "
     "Nat.ceil integer count"),
    ("Q2", "Query",
     "RegretChain takes gamma*e <= R and R <= Lmax*e as hypotheses",
     ["LeanQueryRegretBridgeV1"],
     [],
     "CLOSED: both proved by integrating a decision kernel -- lower for EVERY kernel, "
     "upper for one explicit rule"),
    ("Q3", "Query",
     "measured constants and a grid envelope do not certify the H^2 asymptotic",
     ["LeanQueryGaussianLevelV1", "LeanQueryHellingerIntervalV1",
      "LeanQueryHellingerEnvelopeV1", "LeanQueryTaylorRemainderV1"],
     ["research/worker_P21_query_20260915/P21_query_normalized_lrt.json"],
     "CLOSED: the last step is now proved. LeanQueryMixtureDerivativeV1 supplies "
     "iteratedDeriv_fun_sum -- the scalar-variable counterpart Mathlib lacks -- discharges the "
     "smoothness hypothesis with contDiff_component rather than assuming it, and "
     "iteratedDeriv_mixture identifies the j-th derivative at h=0 with the order-j level sum. "
     "LeanQueryAnalyticLimitV1 adds the analytic closure: the normalised ratio CONVERGES by "
     "dominated convergence and its limit is strictly positive"),
    ("Q4", "Query",
     "'the quadratic class fixes order 2' is too strong: it contains the linear class",
     [],
     ["scripts/P5_query_h4_robustness.py"],
     "CLOSED as a statement: the claim is now relative to the FIRST-ORDER-NEUTRAL "
     "class, and an r=1 design is named as the mandatory comparator"),
    ("Q5", "Query",
     "P5's header says linear while the code uses quadratic",
     [],
     ["scripts/P5_query_h4_robustness.py"],
     "CLOSED: header corrected"),
    ("Q6", "Query",
     "g0 and u were compared without a common normalisation",
     [],
     ["research/worker_P21_query_20260915/P21_query_normalized_lrt.json"],
     "CLOSED: both normalised to E_pi[g^2]=1 before anything is measured"),

    ("S1", "Support",
     "K-class posterior, symmetry-to-minimax and the tuple probability are missing; the "
     "unseen counts are not independent",
     ["LeanSupportSamplingLawV1", "LeanSupportDecideRecoverV1"],
     [],
     "CLOSED: the product law gives Pr(tuple unseen) = (1-s)^N, E prod L = B(1-s)^N by "
     "exchanging two finite sums, the posterior fraction is L/(a+L) from Pascal, and "
     "Bayes <= minimax with equality for an equivariant rule"),
    ("S2", "Support",
     "fixed-K constants contain B = prod b_i; no growing-K law follows",
     ["LeanSupportDecideRecoverV1"],
     ["research/worker_P20_support_20260915/P20_support_growing_k.json"],
     "CLOSED: the a_i=b_i=1, p_i=P/K model gives R_dec = (1/2)(1-P)^N exactly, flat in "
     "K, against a recovery count that grows like K log K"),

    ("T1", "Structural",
     "the saturation lemma takes hconc for EVERY ranking",
     ["LeanStructuralFamilyLowerV1"],
     [],
     "CLOSED: ratio_card_concentrated_on_support weakens it to the support of P"),
    ("T2", "Structural",
     "P14 stores no rankings or weights, so no verifier can replay the certificate",
     ["LeanStructuralFamilyLowerV1", "LeanStructuralFamilyUpperV1"],
     ["research/worker_P19_structural_20260915/P19_structural_construction_replay.json"],
     "CLOSED: the construction is proved for every p,q with q<=p<=q+1 (so every m>=5), "
     "and the artifact stores labelled orderings, weights and defect profiles"),
    ("T3", "Structural",
     "V_path is max-E versus E-max; the ratio grows while the level falls",
     ["LeanStructuralFamilyLowerV1"],
     [],
     "CLOSED: avg_lower is max_k E and path_lower is E max, both stated; the falling "
     "level 2/(m+4) is recorded in both the module and the artifact"),

    ("A1", "Adaptive",
     "P11 is ordinary Gaussian BAI, not the D6 runner",
     [], ["scripts/P11_adaptive_loop_join.py"],
     "CLOSED as a scope statement: the header now says so and disclaims D6 evidence"),
    ("A2", "Adaptive",
     "the epoch spend can exceed the stated cumulative cap",
     [], ["scripts/P11_adaptive_loop_join.py"],
     "CLOSED: the cumulative cap is enforced and the actual cost is reported"),
    ("A3", "Adaptive",
     "two growth factors do not share a transcript; their ratio is not bounded by 4",
     [], ["scripts/P11_adaptive_loop_join.py"],
     "CLOSED as a reading rule: the header states the ratio is not the theorem's"),
    ("A4", "Adaptive",
     "run_once returns an argmax after exhausting max_epoch without a status",
     [], ["scripts/P11_adaptive_loop_join.py"],
     "CLOSED: CERTIFIED / CENSORED / FAILED, certificate_emitted, reason, actual_cost"),
    ("A5", "Adaptive",
     "ConfidenceJoin proves no stopping time, expectation or probability",
     ["LeanAdaptiveStoppingTailV1"], [],
     "CLOSED as far as the question admits. LeanAdaptiveExpectedStoppingV1 PROVES the "
     "layer-cake identity the previous file only cited, so a geometric tail now bounds E[tau] "
     "and not merely the tail sum, and subgaussian_threshold DISCHARGES the per-(arm,count) "
     "concentration input via HasSubgaussianMGF.measure_ge_le. LeanAdaptiveTrackingV1 proves "
     "an allocation with deficit at most 1 EXISTS at every horizon. "
     "LeanAdaptiveOnlineQuotaFailsV1 SETTLES the online question negatively: the "
     "largest-deficit rule is house-monotone but VIOLATES quota, with an exact five-arm "
     "witness whose eleven steps are each verified, so that bound is unattainable online and "
     "an analysis must use one it can prove"),
    ("A6", "Adaptive",
     "fixed doubling gives constant overhead, not a sharp 1/Gamma",
     ["LeanAdaptiveStoppingTailV1"], [],
     "CLOSED AS GRID ARITHMETIC ONLY: grid_overhead is a consequence of an ASSUMED "
     "recurrence and an ASSUMED preceding target below B*.  It shows the factor 4 is an "
     "artefact of ratio 2; it establishes no tracking step and no sharp algorithmic rate"),

    ("G1", "Gates",
     "G02's row_verified checks availability, not claim entailment",
     [], ["scripts/G02_claim_theorem_table.py"],
     "CLOSED: renamed availability_verified, with theorem_claim_verified=False"),
    ("G2", "Gates",
     "G05 read receipts instead of doing a clean build",
     [], ["scripts/G05_clean_build.py"],
     "PARTIAL: the clean-build script now ARCHIVES every local .olean, log and receipt in the closure to legacy/ (never deletes) and rebuilds; 29/29 accepted with all hashes matching.  mathlib stays pinned by rev"),
    ("G3", "Gates",
     "the freeze sidecar has identical before/after runner hashes",
     [], [],
     "CLOSED: the protocol was sealed and lodged on GitHub's own clock (pushed_at 2026-09-15T20:00:17Z) BEFORE the run was launched (20:21:41Z), and the run was executed once on the sealed seeds 811..863.  Primary endpoint, exactly as preregistered: paired mean of (C_lucb - Uniform) restricted N_certificate at H = 131072 over 10000 paired units, -28601.92 with percentile-bootstrap CI95 [-29216.34, -28002.98], 4000 resamples, alpha 0.05 two-sided.  The interval lies entirely below zero, so the sealed hypothesis is SUPPORTED.  Limitation recorded in external_registration.json: the repository is PRIVATE, so a reviewer cannot verify the timestamp without access"),
    ("S-eq", "Support",
     "minimax_eq_of_constant TAKES an equivariant rule; nothing constructed one",
     ["LeanSupportEquivariantDecoderV1"], [],
     "CLOSED: LeanSupportMinimaxLowerV1 supplies the infimum over rules. bayesRisk factors "
     "through the posterior loss; bayes_optimal_lower shows the pointwise argmin rule beats "
     "EVERY rule and bayes_optimal_attained shows such a rule exists, so the infimum is a "
     "minimum; minimax_ge_bayes_optimal chains it with the worst-case bound; and "
     "equivariant_is_minimax states the conclusion as IsLeast over the achievable worst-case "
     "risks. constant_risk_of_symmetry discharges hconst from a transitive relabelling instead "
     "of assuming it"),
    ("D-1", "D6",
     "connect the uncapped profile coefficients to the ACTUAL query means",
     [],
     ["research/worker_P25_d6_20260915/P25_d6_uncapped_means_bridge.json"],
     "CLOSED: the design is now DERIVED. Across all 24 cells the weights depend on (eta, c) "
     "alone and not on (q, mu): w_B = 1 - eta and w_pair = eta/c. budget_exact shows they "
     "spend the unit budget exactly, weights_unique shows the budget constraint together with "
     "the split FORCES them so nothing is fitted, and info_linear with optimum_at_endpoint and "
     "transition_at_equal_price locate the only split at which the optimum is not an endpoint. "
     "The 24/24 match is now a check on an algebraic identity rather than the evidence itself"),
    ("F-opt", "Functional",
     "J(w*) is the value AT w*, not sup_w J(w)",
     ["LeanFunctionalDesignOptimalityV1", "LeanFunctionalSuboptimalWitnessV1"],
     ["research/worker_P27_functional_20260915/P27_functional_suboptimal_certificate.json"],
     "CLOSED by an EXACT witness, not a search: on the eight-cell configuration all 30 "
     "ordered pairs at w~ = (1/5,1/5,1/5,1/5,3/50,1/25,1/25,3/50) are >= 1/160, the "
     "explicit flip attains 1/160, and the endpoint pair at w* gives 49/8397.  Since "
     "49/8397 < 1/160 (gap 557/1343520, 7.1046%), w* is NOT a maximiser.  Gamma* = "
     "sup_w J(w) must NOT be written for c^2/(n(32+2c^2 H_n)).  NOTE: "
     "optimal_iff_no_better_direction quantifies over arbitrary real weight vectors, "
     "not the budget simplex, and must not be cited as a constrained design theorem"),
    ("M-num", "MASTER",
     "U0 < L1 was a 120-digit certificate the reader had to trust a script for",
     ["LeanMasterAnchorInstanceV1"], [],
     "CLOSED: a two-query instance of the SAME model where every number is short -- "
     "U0 = 1/8 (attained, with the dual mixture giving H_e = 1/8 at both queries) and "
     "L1 = 261/1520 -- with the whole chain machine-checked"),
    ("M-rank", "MASTER",
     "the rank-two claim for the gain matrix needs a theorem, not a witness",
     ["LeanMasterGainFactorizationV1"], [],
     "CLOSED: hadamard_square_factor shows the entrywise square of a width-r product is "
     "a width-r^2 product whose left factor is SYMMETRIC in (k,k'), so it lives on the "
     "r(r+1)/2 symmetric pairs -- no rank machinery needed"),

    ("F-G", "MASTER",
     "G_{u,l} = (c_l^T K^{-1} M_u)^2/(2 nu_l kappa_l) must come from real instruments; "
     "a matrix witness on its own is not enough",
     [],
     ["research/worker_P22_master_20260915/P22_master_gain_instruments.json"],
     "CLOSED: M_u is derived as the PROFILED contrast Delta_u a_u/(a_u^T K^{-1} a_u); "
     "the directional-derivative identity dI_u = G_{u,l} - I_u is verified against a "
     "finite difference to 1e-8, and the rank of G is exhibited from instruments "
     "(rank-one B gives rank-one G; rank-two B gives rank 2, bound 3)"),
    ("G12", "Gates",
     "98 names are defined in more than one Lean module",
     [],
     ["research/worker_G14_status_20260915/G12_notation_collisions.json"],
     "CLOSED: the 98 figure was over the WHOLE corpus (321 files).  Restricted to the "
     "headline import closure -- what a manuscript actually cites -- there are 29 "
     "modules, 332 distinct names and exactly 2 collisions: `energy` (3 modules) and "
     "`log_ge_self` (2).  Both are trivial renames"),
    ("G03s", "Gates",
     "all six novelty comparisons were verified=false with no source",
     [],
     ["research/worker_G03_prior_20260915/G03_prior_comparison.json"],
     "PARTIAL, now 4 of 6 at theorem level. Structural, Query and both MASTER priors were "
     "opened and their theorem statements transcribed into G03s_prior_theorem_level_v2.json, "
     "together with the boundary each leaves open. The Structural reading is decisive: the "
     "prior's objective class is f : 2^U -> R_{>=0} while our signed family's prefix sums go "
     "NEGATIVE, so it fails the codomain restriction before accountability is even tested -- a "
     "class separation rather than a constant. Support and Functional remain abstract-only and "
     "cannot support a novelty claim yet"),
    ("B-marg", "Structural",
     "if the theorem is the CONSTRAINED problem, the marginal constraints must be "
     "proved too",
     ["LeanStructuralConstrainedV1"],
     [],
     "CLOSED: LeanStructuralRetainedMarginalV1 carries P3's actual retained-component "
     "trajectory. card_prefixSet proves a length-k prefix of a ranking holds exactly min(k,n) "
     "items; retained_col_sum proves the column sums equal the budget for EVERY menu; "
     "cyclic_retained computes the trajectory in closed form on the cyclic menu, where it is "
     "min(k,m)/m for every item, so the uniform trajectory is REALISABLE and not merely "
     "feasible on paper; and retained_transfer with retained_constrained_eq_free feed that "
     "real object into the generic transfer lemma. A prescribed NON-uniform trajectory remains "
     "open"),
]



def main():
    OUT.mkdir(parents=True, exist_ok=True)
    rows, closed, partial, open_ = [], 0, 0, 0
    for (iid, paper, said, mods, arts, verdict) in ITEMS:
        mod_status, audits = {}, 0
        for m in mods:
            ok, why, n = module_ok(m)
            mod_status[m] = {"ok": ok, "why": why, "audits": n}
            audits += n
        art_status = {a: (REPO / a).exists() for a in arts}
        all_present = all(v["ok"] for v in mod_status.values()) and all(art_status.values())
        stated = verdict.split(":")[0].split(" ")[0].rstrip(",")
        if not all_present and stated in ("CLOSED", "PARTIAL"):
            stated = "OPEN"
            verdict = ("OPEN: evidence named by this row is missing or not accepted -- "
                       + verdict)
        rows.append({
            "id": iid, "paper": paper, "audit_said": said,
            "modules": mod_status, "artifacts": art_status,
            "audits_total": audits,
            "status": stated, "verdict": verdict,
        })
        if stated == "CLOSED":
            closed += 1
        elif stated == "PARTIAL":
            partial += 1
        else:
            open_ += 1
        mark = {"CLOSED": "OK  ", "PARTIAL": "~~  ", "OPEN": "!!  "}[stated]
        print(f"{mark}{iid:3s} [{paper:10s}] {verdict[:96]}")

    out = {
        "gate": "G14",
        "date": "2026-09-15",
        "counts": {"closed": closed, "partial": partial, "open": open_,
                   "total": len(rows)},
        "rule": "a row may claim a module only if its receipt is ACCEPTED and its "
                "recorded hash equals the current source hash; otherwise the row is "
                "forced to OPEN",
        "not_established": [
            "This table certifies availability and compilation, NOT that a module's "
            "prose matches its statement.",
            "The audit counts are summed per row for convenience; they must not be "
            "added up and read as 'the chain is closed'.",
        ],
        "rows": rows,
    }
    path = OUT / "G14_audit_closure_status.json"
    path.write_text(json.dumps(out, indent=1) + "\n")
    print(f"\nCLOSED {closed}   PARTIAL {partial}   OPEN {open_}   of {len(rows)}")
    print(f"artifact: {path}")


if __name__ == "__main__":
    main()
