# CIG-AMF: claim -> theorem -> hypotheses -> artifact -> limits

Build-checked by `scripts/G02_claim_theorem_table.py`: a row is emitted only if every Lean module it names has an ACCEPTED receipt on disk and every artifact it names exists.

## Support

**Claim.** Deciding safely is exponentially cheaper than recovering the world: k0 (1-s)^N <= R_dec <= B (1-s)^N with s = sum_i p_i, against (1/2)(1-p_min)^N <= R_rec <= (sum b_i)(1-p_min)^N.

**Central theorem.** `SupportSamplingLaw.expected_prod_unseen + .good_event_lower + SupportDecideRecover.recover_lower_pointwise/.recover_upper_pointwise + SupportDecideExponent.decide_bracket_pointwise`

**Modules** (27 audited names): `LeanSupportSamplingLawV1`, `LeanSupportDecideRecoverV1`, `LeanSupportDecideExponentV1`, `LeanSupportTupleCountV1`

**Still assumed.** the probability law is now PROVED from the product law (avoid_prob, transversal_mass), so (1-s)^N is no longer checked against the exact law -- it is derived, with NO independence assumed between the per-class unseen counts; the posterior L/(a+L) is proved from Pascal.  What is still TAKEN: minimax_eq_of_constant needs an EQUIVARIANT decoder supplied as a constant-risk hypothesis, and the decoder itself is not constructed

**Artifacts.** `research/worker_P20_support_20260915/P20_support_growing_k.json`, `research/worker_P13_support_20260915/P13_support_decide_exponent.json`

**Limits.** k0 and B = prod b_i are FIXED-K constants; the growing-K law is a different model (a_i = b_i = 1) and its coupon-collector CONSTANT is not proved

## Structural

**Claim.** For EVERY m >= 5 on g_m = (-3,(-1)^p,(+1)^q,3): V_avg = 2/((m+4)(m-1)), V_path = 2/(m+4), V_path/V_avg = m-1.

**Central theorem.** `StructuralFamilyLower.two_le_totalDefect + .avg_lower + .path_lower + StructuralFamilyUpper.exists_one_defect`

**Modules** (37 audited names): `LeanStructuralFamilyLowerV1`, `LeanStructuralFamilyUpperV1`, `LeanStructuralSaturationV1`, `LeanStructuralAvgPathGapV1`

**Still assumed.** NONE for the family law.  The lower bound quantifies over EVERY permutation (no_big_step / two_le_totalDefect) and the m-1 one-defect orderings are CONSTRUCTED for every p, q with q <= p <= q+1, i.e. every m >= 5.  The old hconc/hbal hypotheses are gone; ratio_card_concentrated_on_support keeps a weakened version only as a helper

**Artifacts.** `research/worker_P19_structural_20260915/P19_structural_construction_replay.json`, `research/worker_P3_structural_20260914/P3_avg_path_amplification.json`

**Limits.** the level 2/(m+4) SHRINKS with m: the RATIO grows, the separation LEVEL does not.  What is proved is the FREE problem -- the mixture ranges over all distributions with no marginal constraint

## Functional

**Claim.** At the explicit allocation w*, every flipping alternative costs at least A d^2/2 = c^2/(n(32 + 2c^2 H_n)), and one witness attains it; the known/unknown-variance sandwich is within (1+d/(2 g_min))^2 <= 4.

**Central theorem.** `FunctionalAllocationJoin.gamma_value (= gamma_lower + witness_flips + witness_energy) + .sandwich_ratio`

**Modules** (30 audited names): `LeanFunctionalAllocationJoinV1`, `LeanFunctionalHeterogeneousInstanceV1`, `LeanFunctionalGeometryDischargeV1`, `LeanFunctionalHeterogeneousLowerV1`

**Still assumed.** no geometric inequality is taken: mean_gap and mean_diff_lt_one are derived from the cell layout, and energyU_ge_pairV is IMPORTED AND INVOKED rather than restated.  What is still TAKEN: FlipsU uses <=, so the witness attains the minimum for THAT alternative set; for strict rank inversion it gives an infimum

**Artifacts.** `research/worker_P10_functional_20260914/P10_functional_instantiation.json`, `research/worker_P4_functional_20260914/P4_functional_topology.json`

**Limits.** known variances; the domain g >= d/2 is sharp.  A d^2/2 is the value AT w* and is NOT shown optimal over the design polytope, so it must not be written Gamma* = sup_w J(w)

## D6

**Claim.** The B-scalar is never blind, so the phase story is an ASYMMETRY, not disjoint blindness; and the full design strictly beats the two-class family in 6 of 12 certified cells.

**Central theorem.** `D6ScalarInformation.blindness_asymmetry + .clipped_min + .dual_over_all_queries`

**Modules** (14 audited names): `LeanD6ScalarInformationV1`, `LeanD6ThreeClassPhaseV1`

**Still assumed.** dual_over_all_queries is a certificate SHAPE: it is quantified over EVERY legal query, but no specific mixture rho or value V is exhibited in Lean.  The strict separation L_full > U_two is an exact rational certificate in the artifact, not a Lean theorem

**Artifacts.** `research/worker_P18_d6_20260915/P18_d6_full_vs_two.json`, `research/worker_P7_d6_fulldesign_20260914/P7_d6_full_design.json`, `research/worker_P1_d6_phase_20260914/P1_d6_phase_law.json`

**Limits.** the alternative family is (d, x) and the symmetry orbits; t_end is NOT the phase boundary and NO phase boundary is certified; sup_err_grid is a grid supremum, not a continuous one

## Query

**Claim.** The admissible measurement fixes the leakage order r; H^2 has order h^{2r}; N* = Theta(h^{-2r}) as an integer count; and the regret of a real decision is pinned between two powers of the same affinity.

**Central theorem.** `QueryGaussianLevel.levelSum_ne_zero + QueryHellingerInterval.hellinger_lower_from_interval + QueryHellingerEnvelope.envelope_integrable + QuerySampleComplexity.matching_rate + QueryRegretBridge.regret_ge_gamma_error/.lrt_regret_le`

**Modules** (51 audited names): `LeanQueryGaussianLevelV1`, `LeanQueryHellingerIntervalV1`, `LeanQueryHellingerEnvelopeV1`, `LeanQuerySampleComplexityV1`, `LeanQueryRegretBridgeV1`, `LeanQueryAffinityTestingV1`

**Still assumed.** L <= 2H^2 is now PROVED (neg_log_le_two), and both expectation steps of the regret reduction are now PROVED by integrating a decision kernel -- lower for EVERY kernel, upper for ONE explicit rule.  What is still TAKEN: the uniform Taylor remainder, so the interval lower bound receives its gap |a_E||h|^r/2 as an input and the constant c_+ remains MEASURED

**Artifacts.** `research/worker_P21_query_20260915/P21_query_normalized_lrt.json`, `research/worker_P15_query_20260915/P15_query_hellinger_order.json`, `research/worker_P16_query_20260915/P16_query_regret_chain.json`, `research/worker_P9_query_20260914/P9_query_transcript_complexity.json`

**Limits.** one pair of worlds, one noise level, r in {1,2}; the equal-amplitude comparison has a CROSSOVER at h* = 0.1133, above which the constants dominate the order -- sample counts at h = 0.6 are not order evidence. The prior is equal (Bayes risk), not worst-case minimax

## MASTER

**Claim.** Three separate results: the symmetric-family price threshold c* = (m-1)^2/(m+3)^2; a mandatory anchor at c0 = 1/10 on the finite instance; and the full-class calibration rate Gamma* = Delta^2/(2K(sqrt m + sqrt kappa)^2).

**Central theorem.** `MasterAnchorThreshold.global_upper + .below_threshold + MasterAnchorCertificate.anchor_free_upper + .anchor_mandatory + MasterCalibrationLaw.calibration_rate_upper/.attained + .hidden_shift_witness`

**Modules** (44 audited names): `LeanMasterCalibrationLawV1`, `LeanMasterAnchorCertificateV1`, `LeanMasterAnchorThresholdV1`, `LeanMasterActiveSetV1`, `LeanMasterGroupCalibrationV1`

**Still assumed.** anchor_mandatory assumes NO optimality of the anchored design and needs NO value of the game; anchor_free_upper allows several shifts per alternative, which is the fix to the multiplier extraction.  What is still TAKEN: U0 = 0.013773103740 and L1 = 0.014042993094 are exact-rational certificates from P12, not Lean numbers; the full-class rate assumes equal variances, equal prices and a common gap; the gain matrix G_{u,l} is bridged from real instruments NUMERICALLY (P22), not in Lean

**Artifacts.** `research/worker_P12_master_20260915/P12_master_anchor_required.json`, `research/worker_P17_master_20260915/P17_master_full_class.json`, `research/worker_P22_master_20260915/P22_master_gain_instruments.json`, `research/worker_P6_master_20260914/P6_master_group_calibration.json`

**Limits.** the three results are THREE DIFFERENT PROBLEMS and none implies another; the old 0.118 is none of them; P6's four-alternative game is not the threshold class (hidden_shift_witness shows why)

## Adaptive

**Claim.** Scheduler + revalidation + stopping compose: the loop is sound and spends less than 4 B*.

**Central theorem.** `AdaptiveLoopJoin.doubling_factor + AdaptiveConfidenceJoin.guarantee_on_event`

**Modules** (6 audited names): `LeanAdaptiveLoopJoinV1`, `LeanAdaptiveConfidenceJoinV1`

**Still assumed.** ONLY the composition is proved.  P(E^c) <= delta for the GLR threshold, the tracking step, and the tail of the stopping time are all open; the theorem is a statement ON the event

**Artifacts.** `research/worker_P11_adaptive_20260914/P11_adaptive_loop_join.json`

**Limits.** the harness is ORDINARY Gaussian BAI, not the D6 runner, and is no evidence about D6's expected Gamma; two growth factors do not share a transcript, so their cost ratio is not bounded by the doubling theorem; runs now report CERTIFIED / CENSORED / FAILED and the actual cost under an enforced cumulative cap
