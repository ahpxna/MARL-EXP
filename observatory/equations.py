"""Every equation the six chains argue about, declared with every symbol.

This file is the contract between the theory and the measurement store.  If a
quantity appears in a report, it appears here; if it appears here, some probe
must be able to emit it or explicitly mark it skipped/blocked.

``status_note`` records the ledger disposition as of 2026-09-04.  It is
deliberately *data*, not a filter: killed and demoted equations are still
measured, because the ledger's own principle is that a failed branch stays in
the record and because a killed universal law is often a live conditional one.
"""
from __future__ import annotations

from .schema import Equation, declare

# =====================================================================
# MASTER  (chain 01)
# =====================================================================

MASTER_SUPPORT_DEFICIT = declare(Equation(
    "MASTER.deficit_identity", "MASTER",
    "d_Omega(T) = M(T) - F_Omega(T) = e_plus(T) + e_minus(T) >= 0",
    ("M", "F_Omega", "d_Omega", "e_plus", "e_minus", "sum_check",
     "identity_residual", "nonneg_holds", "omitted_card"),
    kind="identity", status_note="ACTIVE",
))

MASTER_ZETA_HALF = declare(Equation(
    "MASTER.zeta_half", "MASTER",
    "r_Omega(S_C) - r*_Omega <= zeta_k^def / 2",
    ("topc_radius", "optimal_radius", "topc_regret", "zeta_def", "bound",
     "slack", "ratio", "holds"),
    status_note="ACTIVE CERTIFICATE",
))

MASTER_E_HALF = declare(Equation(
    "MASTER.global_E_half", "MASTER",
    "r_Omega(S_C) - r*_Omega <= E/2  with E = e_plus + e_minus over all relations",
    ("topc_regret", "E", "bound", "slack", "ratio", "holds"),
    status_note="ACTIVE GLOBAL BACKSTOP",
))

MASTER_LP = declare(Equation(
    "MASTER.lp_lower_bound", "MASTER",
    "r_Omega(S_C) - r*_Omega <= r_Omega(S_C) - LB_LP,  LB_LP <= r*_Omega",
    ("topc_radius", "optimal_radius", "LB_LP", "bound", "slack", "lp_valid", "holds"),
    status_note="ACTIVE COMPUTATIONAL ROUTE",
))

MASTER_CERT_HIERARCHY = declare(Equation(
    "MASTER.certificate_min", "MASTER",
    "min{ zeta_k^def/2 , E/2 , r_Omega(S_C) - LB_LP } is the operative certificate",
    ("zeta_half", "E_half", "lp_gap", "min_certificate", "argmin_route",
     "topc_regret", "is_vacuous", "tightness_ratio"),
    kind="definition", status_note="ACTIVE HIERARCHY",
))

MASTER_GAMMA = declare(Equation(
    "MASTER.gamma_operational", "MASTER",
    "L(Shat) - L* <= Gamma + zeta_k^def/2 + 2 eta   for Gamma in {oracle, op, box}",
    ("Gamma_oracle", "Gamma_op", "Gamma_box", "zeta_half", "eta",
     "loss_gap", "bound_op", "bound_box", "box_le_op", "box_strictly_tighter",
     "slack_op", "slack_box", "holds_op", "holds_box"),
    status_note="Gamma_box PROVED TIGHTER; Gamma_op STILL THE FROZEN RUNTIME",
))

MASTER_COVERAGE = declare(Equation(
    "MASTER.coverage_frontier", "MASTER",
    "certified fraction and false-safe rate as functions of declared tolerance eps",
    ("epsilon", "certified", "abstained", "false_safe", "certified_fraction",
     "fallback_fraction", "false_safe_rate", "n_decisions", "regret_if_certified"),
    kind="definition", status_note="PROMOTED EMPIRICAL FRONTIER",
))

MASTER_TCC_COMPLETION = declare(Equation(
    "MASTER.typed_completion", "MASTER",
    "C*(C_t) = min_{A subset E} { sum_{e in A} c(e) : A discharges O_t^active }",
    ("n_obligations", "n_evidence", "completion_cost", "greedy_cost",
     "greedy_ratio", "is_complete", "n_active_after", "cheapest_single",
     "cost_spread", "types_used"),
    kind="definition", status_note="TCC-3 COMPILED (existence); complexity OPEN",
))

MASTER_INDISPENSABILITY = declare(Equation(
    "MASTER.direct_product", "MASTER",
    "for each type t: O_t(M_t^0)=O_t(M_t^1) and G_t(M_t^0) cap G_t(M_t^1) = empty",
    ("type_index", "reduced_evidence_equal", "good_sets_disjoint",
     "locally_indispensable", "n_types_indispensable", "product_incompatible",
     "controller_exists"),
    kind="predicate", status_note="PROVED (five types)",
))

MASTER_ELIMINATION = declare(Equation(
    "MASTER.typed_elimination", "MASTER",
    "structural conditions under which a typed obligation is discharged for free",
    ("interaction_eliminated", "support_eliminated", "ranking_eliminated",
     "reference_eliminated", "n_eliminated", "n_remaining",
     "mixed_diff_max", "deficit_max", "interval_separation", "reference_error_max"),
    kind="predicate", status_note="PROVED (dual side)",
))

MASTER_BUDGET_SPLIT = declare(Equation(
    "MASTER.two_source_split", "MASTER",
    "R(x) = A/sqrt(x) + B/sqrt(N-x);  x* = N A^{2/3} / (A^{2/3} + B^{2/3})",
    ("A", "B", "N", "x_star", "R_at_star", "R_min_grid", "grid_gap",
     "closed_form_matches_grid", "s_star_fraction"),
    kind="identity", status_note="PROVED IN P13 (continuous relaxation only)",
))

# =====================================================================
# FUNCTIONAL  (chain 02)
# =====================================================================

FUNC_GAUGE = declare(Equation(
    "FUNC.gauge_error", "FUNCTIONAL",
    "delta_Q^circ = inf_c ||Qhat - Q - c||_inf = (1/2) osc(Qhat - Q)",
    ("delta_circ", "sup_error", "gauge_shift", "sup_minus_gauge",
     "n_actions", "osc_Q", "osc_Qhat"),
    kind="identity", status_note="ACTIVE PRIMITIVE",
))

FUNC_LAMBDA_C = declare(Equation(
    "FUNC.local_extremal", "FUNCTIONAL",
    "lambda_C = delta_Q^circ / g < 1/2  ==>  (argmax_hat, argmin_hat) = (argmax, argmin)",
    ("delta_circ", "g_plus", "g_minus", "g", "lambda_C", "threshold",
     "certified", "argmax_match", "argmin_match", "both_match",
     "violation", "unique_max", "unique_min", "margin_to_threshold"),
    status_note="ACTIVE SHARP SUFFICIENT CONDITION",
))

FUNC_CAPACITY_TRANSFER = declare(Equation(
    "FUNC.capacity_transfer", "FUNCTIONAL",
    "|C(Qhat) - C(Q)| <= 2 delta_Q^circ",
    ("C_hat", "C_true", "abs_error", "bound", "slack", "ratio", "holds"),
    status_note="ACTIVE",
))

FUNC_DIRECTION_TRANSFER = declare(Equation(
    "FUNC.direction_transfer", "FUNCTIONAL",
    "|D_w(Qhat) - D_w(Q)| <= ||w||_1 delta_Q^circ ;  lambda_D < 1 certifies the sign",
    ("D_hat", "D_true", "abs_error", "w_l1", "bound", "slack", "holds",
     "lambda_D", "sign_margin", "sign_match", "sign_certified", "sign_violation"),
    status_note="ACTIVE SAFE SIGN CERTIFICATE",
))

FUNC_TOPK_PAIR = declare(Equation(
    "FUNC.topk_pair_order", "FUNCTIONAL",
    "C_j - C_l > 2 delta_{Q,j}^circ + 2 delta_{Q,l}^circ  ==>  the pair order is safe",
    ("C_j", "C_l", "margin", "delta_j", "delta_l", "bound", "slack",
     "certified", "order_correct", "violation"),
    status_note="ACTIVE GLOBAL CONDITION",
))

FUNC_TOPK_GLOBAL = declare(Equation(
    "FUNC.topk_boundary", "FUNCTIONAL",
    "lambda_TopK,Q = boundary score uncertainty / Delta_TopK",
    ("delta_topk", "boundary_uncertainty", "lambda_topk", "topk_match",
     "boundary_unique", "certified", "violation", "k"),
    status_note="ACTIVE SECOND MARGIN",
))

FUNC_TWO_LEVEL = declare(Equation(
    "FUNC.two_level_chain", "FUNCTIONAL",
    "delta_Q^circ -> lambda_C -> within-relation identity -> Delta_TopK -> lambda_TopK,Q",
    ("delta_circ", "lambda_C", "local_ok", "delta_topk", "lambda_topk",
     "global_ok", "local_implies_global", "counterexample_local_ok_global_bad"),
    kind="predicate", status_note="ACTIVE: local does NOT imply global",
))

FUNC_STOPPING = declare(Equation(
    "FUNC.certification_complexity", "FUNCTIONAL",
    "N_cert(q,delta) = inf{ n : query q is certified after n interventions }",
    ("n_cert", "certified", "budget_exhausted", "geometry_stratum",
     "delta_topk", "g", "false_certificate", "n_uniform", "n_targeted",
     "targeted_saving_ratio"),
    kind="definition", status_note="PROMOTED PRIMARY ENDPOINT",
))

FUNC_MAINTENANCE = declare(Equation(
    "FUNC.selective_maintenance", "FUNCTIONAL",
    "safe refresh set R:  dbar_j(R) + dbar_l(R) < L_j - U_l  for all j in S, l not in S",
    ("d_j", "d_l", "r_j", "r_l", "L_j", "U_l", "reserve", "lhs", "rhs",
     "slack", "safe", "infeasible_maintenance", "refresh_size",
     "refresh_cost", "full_refresh_cost", "cost_ratio", "monotone_holds"),
    status_note="PROMOTED; nonzero post-refresh uncertainty required",
))

FUNC_VARIANCE = declare(Equation(
    "FUNC.unknown_variance", "FUNCTIONAL",
    "(1-rho) sigma <= sigmahat <= (1+rho) sigma  ==>  plug-in design cost <= ((1+rho)/(1-rho))^2",
    ("rho", "bound_factor", "observed_factor", "slack", "holds",
     "stable_extrema_assumed", "selection_error_present"),
    status_note="PROVED CONDITIONAL (stable-extrema only)",
))

FUNC_COVARIANCE = declare(Equation(
    "FUNC.covariance_design", "FUNCTIONAL",
    "Var(v^T Qhat) = v^T Sigma_Q v ;  diagonal reduction can reverse design order",
    ("var_full", "var_diag", "full_diag_ratio", "reversal_witness",
     "contrast_kind", "n_designs", "order_agrees"),
    status_note="ACTIVE; diagonal sufficiency KILLED in general",
))

# =====================================================================
# SUPPORT  (chain 03)
# =====================================================================

SUP_RADIUS = declare(Equation(
    "SUP.exact_radius", "SUPPORT",
    "r_Omega(S) = (1/2) osc_{a in Omega} sum_{j not in S} f_j(a_j)",
    ("radius", "k", "omitted_card", "omega_size", "omega_density",
     "is_cartesian", "osc_omitted", "min_omitted", "max_omitted"),
    kind="definition", status_note="ACTIVE EXACT OBJECT",
))

SUP_MODULAR = declare(Equation(
    "SUP.modular_formula", "SUPPORT",
    "r_Omega(S) = (1/2) sum_{j not in S} C_j   holds only on co-extremizable support",
    ("radius_exact", "radius_modular", "gap", "ratio", "holds",
     "co_extremizable", "sum_spans", "n_relations"),
    status_note="KILLED as a universal law; ACTIVE in the product/coext regime",
))

SUP_DEFICIT = declare(Equation(
    "SUP.deficit", "SUPPORT",
    "d_Omega(T) = M(T) - F_Omega(T) = e_plus(T) + e_minus(T)",
    ("M", "F_Omega", "d_Omega", "e_plus", "e_minus", "identity_residual",
     "nonneg_holds", "T_card"),
    kind="identity", status_note="ACTIVE SHARPENING",
))

SUP_BRACKETS = declare(Equation(
    "SUP.support_brackets", "SUPPORT",
    "Omega^- subset Omega subset Omega^+  ==>  r_{Omega^-}(S) <= r_Omega(S) <= r_{Omega^+}(S)",
    ("r_lower", "r_actual", "r_upper", "bracket_width", "monotone_holds",
     "lower_size", "actual_size", "upper_size", "interval_contains_truth"),
    status_note="ACTIVE UNCERTAINTY ROUTE",
))

SUP_PERTURB = declare(Equation(
    "SUP.component_perturbation", "SUPPORT",
    "|rhat_Omega(S) - r_Omega(S)| <= sum_{j not in S} delta_j^circ",
    ("r_hat", "r_true", "abs_error", "sum_delta", "bound", "slack", "ratio",
     "holds", "sup_norm_alternative", "gauge_beats_supnorm"),
    status_note="ACTIVE GAUGE-INVARIANT FORM",
))

SUP_CRITICAL_CELL = declare(Equation(
    "SUP.critical_cell", "SUPPORT",
    "cell a is critical when two supports differing only at a have disjoint eps-good sets",
    ("cell_id", "is_critical", "n_critical", "n_cells", "critical_fraction",
     "good_set_size_small", "good_set_size_large", "sets_disjoint", "epsilon"),
    kind="predicate", status_note="PROVED (SUP-B1)",
))

SUP_QUERY_COMPLEXITY = declare(Equation(
    "SUP.separating_query_set", "SUPPORT",
    "Q*_eps = min |Q| s.t. O_Q separates every decision-incompatible support pair",
    ("q_star", "n_worlds", "n_incompatible_pairs", "n_cells", "epsilon",
     "greedy_size", "greedy_ratio", "lower_bound_pairs", "cover_feasible"),
    kind="definition", status_note="PROVED on the two-world witness (Q* = 1)",
))

SUP_TEST_COVER = declare(Equation(
    "SUP.test_cover_reduction", "SUPPORT",
    "separating query set == (partial) Test Cover on the hypergraph e_a = {Omega : a in Omega}",
    ("n_vertices", "n_edges", "max_edge_size_r", "required_pairs",
     "greedy_size", "lower_bound_r", "lb_over_greedy", "ln_bound",
     "greedy_over_ln", "is_full_test_cover", "reduction_valid"),
    kind="definition", status_note="NEW: classical reduction, not a novelty claim",
))

# =====================================================================
# STRUCTURAL  (chain 04)
# =====================================================================

STR_OPTIMA = declare(Equation(
    "STR.budget_optima", "STRUCTURAL",
    "O_k = argmin_{|S|=k} r_Omega(S);  the layered optimum family",
    ("k", "opt_value", "n_optima", "unique", "optimum_set",
     "is_topc", "topc_value", "topc_regret_k"),
    kind="definition", status_note="ACTIVE",
))

STR_COEXT_MODULAR = declare(Equation(
    "STR.coext_iff_modular", "STRUCTURAL",
    "global co-extremizability <==> all-subsets modularity  ==> Top-C exact at every budget",
    ("co_extremizable", "all_subsets_modular", "iff_holds",
     "topc_exact_all_budgets", "implication_holds", "n_subsets_checked",
     "worst_modularity_gap"),
    kind="predicate", status_note="PROVED",
))

STR_RANKABLE = declare(Equation(
    "STR.scalar_prefix_rankable", "STRUCTURAL",
    "exists a ranking whose every prefix is optimal <==> the optima admit a nested chain",
    ("scalar_prefix_rankable", "nested_optimal_chain", "iff_holds",
     "topc_exact", "rankable_but_not_topc", "topc_but_not_coext",
     "n_incomparable_optima", "taxonomy_class"),
    kind="predicate", status_note="PROVED (SR0)",
))

STR_CHI = declare(Equation(
    "STR.prefix_cover_dimension", "STRUCTURAL",
    "chi_prefix(f,eps) = min number of rankings whose prefixes hit an acceptable set in every layer",
    ("chi_prefix", "epsilon", "m", "upper_bound_m_plus_1", "lower_bound",
     "sandwich_holds", "n_rankings_tried", "layers_covered", "exact"),
    kind="definition", status_note="NEW CORE OBJECT",
))

STR_STAIRCASE = declare(Equation(
    "STR.staircase_family", "STRUCTURAL",
    "for F_r with m = 2r:  r <= chi_prefix(F_r,0) <= 2r+1, hence Theta(m)",
    ("r", "m", "chi_lower", "chi_upper", "chi_measured", "sandwich_holds",
     "n_zero_radius_sets", "zero_sets_are_blocks", "unique_optimum_per_layer",
     "antichain_size", "pairwise_incomparable"),
    status_note="PROVED 4-Sep",
))

STR_MAXMODULAR = declare(Equation(
    "STR.max_of_modular", "STRUCTURAL",
    "2 r_Omega(S) = max_{a,b} [ sum_j d_{ab,j} - sum_{j in S} d_{ab,j} ]",
    ("radius_doubled", "max_modular_value", "identity_residual", "holds",
     "argmax_pair", "n_scenarios", "active_scenario_count"),
    kind="identity", status_note="ACTIVE BRIDGE (under-exploited)",
))

STR_NESTED_REGRET = declare(Equation(
    "STR.nested_regret", "STRUCTURAL",
    "R_nested = min_pi max_k [ r_Omega(P_k(pi)) - r*_k ]   vs   eps_allopt and m eps_allopt",
    ("R_nested", "eps_allopt", "ratio_to_eps", "ratio_to_m_eps",
     "raw_bound_holds", "scaled_bound_holds", "m", "best_ranking",
     "worst_budget", "incremental_competitive_ratio"),
    status_note="raw KILLED; scaled OPEN (collides with incremental maximization)",
))

# =====================================================================
# D6  (chain 05)
# =====================================================================

D6_SURROGATE = declare(Equation(
    "D6.additive_surrogate", "D6",
    "A_q(a) = sum_j Q_j^q(a_j) - (m-1) b   with b = E_q F",
    ("b", "m", "A_min", "A_max", "surrogate_span", "is_exactly_additive",
     "recovers_F_when_additive", "max_abs_A"),
    kind="definition", status_note="ACTIVE",
))

D6_WORLD_APPROX = declare(Equation(
    "D6.world_approximation", "D6",
    "||F - A_q||_inf <= (m-1) delta_square",
    ("sup_error", "delta_square", "m", "bound", "slack", "ratio", "holds",
     "is_sharp", "argmax_action"),
    status_note="PROVED AND SHARP",
))

D6_DECISION = declare(Equation(
    "D6.decision_transfer", "D6",
    "L_F(S_C) - L*_F <= 2 (m-1) delta_square",
    ("loss_selected", "loss_optimal", "decision_regret", "delta_square",
     "bound", "slack", "ratio", "holds", "m"),
    status_note="ACTIVE HEADLINE",
))

D6_HALF_FACTOR = declare(Equation(
    "D6.half_factor", "D6",
    "J(F,q) = (L_F(S_C) - L*_F) / ((m-1) delta_square) <= 1/2 ?",
    ("J", "numerator", "denominator", "threshold", "holds", "margin",
     "best_seen", "killed", "m", "arity"),
    status_note="OPEN: the portfolio's single remaining sorry",
))

D6_KAPPA_DI = declare(Equation(
    "D6.decision_interaction_complexity", "D6",
    "kappa_DI(C) = sup { l_C(F) : G_C F <= 0, ||Delta F||_inf <= 1 },  l_C(F)=2[L_F(S)-L_F(T)]",
    ("l_C", "kappa_observed", "m_minus_1", "exceeds_m_minus_1", "slack",
     "ratio", "normalized", "balanced", "strict_topc", "arity",
     "reference_is_point_mass", "reference_mass_check"),
    status_note="universal m-1 law FALSIFIED 4-Sep; conditional version OPEN",
))

D6_NEW1 = declare(Equation(
    "D6.symmetric_difference", "D6",
    "D(S,T) <= |S \\ T| delta_square   (the NEW-1 direct endpoint patch bound)",
    ("D_ST", "sym_diff_size", "delta_square", "bound", "slack", "ratio",
     "holds", "is_balanced_complement", "m", "k"),
    status_note="PROVED; closes all non-exceptional geometry",
))

D6_PROFILE = declare(Equation(
    "D6.centered_interaction_profile", "D6",
    "psi_{i,u}^{u0}(z) = [F(z_{i<-u}) - F(z_{i<-u0})] - [Q_i^q(u) - Q_i^q(u0)]",
    ("coordinate", "anchor", "anchor_is_zero", "gauge_invariant",
     "profile_max", "profile_min", "profile_span", "n_contexts", "n_actions"),
    kind="definition", status_note="NEW INVARIANT 4-Sep",
))

D6_RANKONE = declare(Equation(
    "D6.rank_one_geometry", "D6",
    "coordinate i is rank one iff every 2x2 minor psi_{i,u}(x)psi_{i,v}(y) - psi_{i,u}(y)psi_{i,v}(x) vanishes",
    ("coordinate", "max_abs_minor", "is_rank_one", "n_profile_levels",
     "contrast_spectrum_size", "all_coordinates_rank_one", "two_profile",
     "binary_alphabet", "witness_minor_u", "witness_minor_v"),
    kind="predicate", status_note="NEW; rank-one sufficiency conjecture OPEN",
))

D6_APPLICABILITY = declare(Equation(
    "D6.applicability_gate", "D6",
    "finite full Cartesian action space + normalized nonnegative product weights",
    ("cartesian_support", "weights_nonnegative", "weights_normalized",
     "reference_conditional", "missing_cells", "applicable",
     "would_have_been_silently_normalized"),
    kind="predicate", status_note="ACTIVE FAIL-CLOSED CONTRACT",
))

# =====================================================================
# QUERY  (chain 06)
# =====================================================================

QRY_SUFFICIENCY = declare(Equation(
    "QRY.sufficiency", "QUERY",
    "S(M1) = S(M2)  ==>  T(M1) = T(M2)   for all M1,M2 in the declared class",
    ("n_models", "n_summary_classes", "sufficient", "n_violating_pairs",
     "worst_target_gap", "summary_kind", "target_kind"),
    kind="predicate", status_note="ACTIVE DEFINITION",
))

QRY_MINIMAX = declare(Equation(
    "QRY.quantitative_floor", "QUERY",
    "max_i |psi(s) - T(M_i)| >= (1/2) |T(M1) - T(M2)|",
    ("t1", "t2", "target_gap", "floor", "best_predictor_error",
     "achieved_by_midpoint", "slack", "holds", "violation"),
    status_note="PROVED QUANTITATIVE UPGRADE",
))

QRY_REPRESENTATION = declare(Equation(
    "QRY.representation_necessity", "QUERY",
    "uniform eps-good decisions on a fibre require intersection of good sets to be non-empty",
    ("fibre_size", "epsilon", "common_good_exists", "intersection_size",
     "uniform_low_regret_possible", "n_fibres", "n_empty_intersections"),
    kind="predicate", status_note="PROVED CONVERSE DIRECTION",
))

QRY_TRANSFER = declare(Equation(
    "QRY.transfer_regret", "QUERY",
    "R_{m->q}(M) = R_q(M, dhat_{m->q}(M)) - R_q(M, d*_q(M))",
    ("transfer_regret", "native", "method", "query", "is_native_method",
     "native_regret", "foreign_regret", "native_advantage",
     "normalized_regret", "rank_correlation", "topk_overlap"),
    kind="definition", status_note="PROMOTED PRIMARY METRIC",
))

QRY_GATES = declare(Equation(
    "QRY.three_gates", "QUERY",
    "capability -> identifiability -> transfer regret;  cell in {BLOCKED, INSUFFICIENT, EVALUABLE}",
    ("capability_ok", "identifiable", "cell_status", "regret_attached",
     "n_blocked", "n_insufficient", "n_evaluable", "n_cells",
     "matrix_complete", "readiness"),
    kind="predicate", status_note="ACTIVE FAIL-CLOSED CONTRACT",
))

QRY_BUDGET = declare(Equation(
    "QRY.matched_budget", "QUERY",
    "B_m(M) <= B for all compared methods;  report R^full and R^B",
    ("budget_used", "budget_cap", "within_budget", "regret_full",
     "regret_matched", "budget_ratio", "advantage_from_budget"),
    status_note="REQUIRED FAIRNESS CONDITION",
))

# =====================================================================
# CROSS-CHAIN
# =====================================================================

X_SEPARATION = declare(Equation(
    "X.interaction_vs_support", "CROSS",
    "interaction/nonadditivity is independent of support coupling",
    ("residual_supnorm", "delta_square", "co_extremizable", "support_density",
     "additive_and_coupled", "interacting_and_cartesian", "quadrant"),
    kind="predicate", status_note="ACTIVE STRUCTURAL LESSON",
))

X_CERT_COVERAGE = declare(Equation(
    "X.certificate_coverage", "CROSS",
    "coverage of every certificate route as a function of family, m and tolerance",
    ("route", "family", "m", "epsilon", "fires", "vacuous", "correct",
     "false_safe", "coverage", "mean_slack", "median_slack"),
    kind="definition", status_note="EMPIRICAL LAW CANDIDATE",
))

X_INVARIANT = declare(Equation(
    "X.cross_chain_invariant", "CROSS",
    "candidate relations between quantities of different chains, measured not assumed",
    ("lhs_symbol", "rhs_symbol", "lhs_value", "rhs_value", "relation",
     "holds", "slack", "support_count", "violation_count"),
    kind="predicate", status_note="MINING TARGET",
))
