# High-Value Extension Theorem Statements

All theorem names below refer to new immutable-baseline extensions in `work/p12/`.

## MASTER reference uncertainty

- `RU1_expectation_reference_error`: valid finite kernels plus rowwise `TV <= eps` imply `|E_kappa H - E_kappahat H| <= osc(H) eps` at every source action.
- `RU2_chi_reference_error`: the induced oscillations differ by at most `2 osc(H) eps`.
- `RU2_factor_two_sharp_witness`: a valid Fin-2 witness attains equality in RU2.
- `RU3_primitive_score_reference_interval`: primitive isolation mismatch is bounded by computable `chi(kappahat) + 2 osc(H) eps`.
- `RU4_same_target_error_composition`: statistical, reference, support, and model bounds compose through `SameTargetScoreChain` into `scoreCovered` for one terminal score.
- `RU5_composed_reference_uncertainty_MASTER`: RU4 coverage is supplied to the frozen `FULLY_INSTANTIATED_OPERATIONAL_MASTER`.

## D6

- `S1_D6_approximation_constant_sharp`: exact product world showing the universal `(m-1)` approximation multiplier cannot be decreased.
- `Q1_coordinate_specific_pointwise_bound`, `Q1_product_coordinate_specific_bound`: replace uniform delta by the exact telescoping sum of coordinate moduli.
- `Q2_q_averaged_absolute_uniform_bound`: pointwise residual is bounded by q-averaged absolute hybrid mixed differences.
- `Q2_q_averaged_absolute_scalar_uniform_bound`: taking the finite maximum over source worlds yields a computable scalar uniform modulus.
- `Q3_signed_average_bound`: pointwise residual is bounded by the sum of absolute signed q-averaged hybrid terms.
- `signed_le_absolute_telescoping`: the signed term is no larger than its absolute-average counterpart.
- `Q4_distributional_residual_bound`: q-mean absolute residual inherits the q-sensitive bound.
- `qL1CompressionLoss_transfer`: a distributional compression objective is 1-Lipschitz in q-mean absolute world error.
- `Q5_distributional_decision_regret`: conditional surrogate optimality yields a separate distributional `2 * mean-error` regret theorem.

## Query representation necessity

- `QN1_same_summary_rule_implies_common_good`: one summary-based epsilon-optimal rule on two same-summary worlds implies their good-decision sets intersect.
- `QN2_disjoint_good_sets_force_representation_separation`: disjoint good sets force unequal summaries.
- `QN3_distinct_unique_subset_optima_have_disjoint_good_sets`: unique subset optima with regret margin instantiate QN2.
- `QN4_uniform_fiber_optimality_requires_common_good_decision`: uniform epsilon-optimality on a summary fiber produces one common good decision.
- `QN4_common_good_decision_is_sufficient_on_fiber`: the converse construction for a fixed fiber.

## Reference identifiability

- `RI1_observed_source_indistinguishable`: two valid kernels agree on every observed source action and differ at an unobserved action.
- `RI2_indistinguishable_kernels_different_chi`: the two kernels induce chi values 0 and 1.
- `RI2_downstream_top1_changes`: the same witness reverses a unique Top-1 relation decision.

## Functional covariance design

- `FCOV1_D_error_uses_w`: the D error is the linear functional of response error with coefficient w.
- `FCOV2_stable_extrema_C_uses_unit_contrast`: stable-extrema C error uses `e_aplus - e_aminus`.
- `FCOV3_diagonal_reduction`: a diagonal quadratic form reduces to the independent-head variance sum.
- `FCOV_design_misranking_witness`: two explicitly PSD Fin-2 designs are ranked oppositely by diagonal-only and full covariance.

## Structural pivot

- `SRALG_subset_state_count`: the subset lattice has `2^m` states.
- `SRALG_ranking_search_count`: full ranking enumeration has `m!` candidates.
- `STAX_actual_support_radius_three_way_taxonomy`: one theorem packages the three actual support-radius W1/W2/W3 strictness witnesses.
