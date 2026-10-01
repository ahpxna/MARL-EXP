# Full-corpus audit and novelty review, 2026-09-27

Research-only pass requested by the user ("lượt này chưa làm gì cả, mà chỉ research"). Nothing in the
manuscripts, Lean, or scripts is changed by this pass. Notes are written as the reading proceeds.

## 0. State at the start

- Lean: 754 files in `work/p13_conjectures`, 158,046 lines, 7,704 theorem/lemma declarations,
  2,602 def/structure/abbrev/inductive declarations.
- Local `.lake/build` has oleans for 323 of 754 modules (431 missing, 6 older than their source).
  The authoritative compiled state is the frozen gate directories in `work/gate_runs/<RUN>/`, each
  built from scratch.
- Last complete full gate: `full7_20260925` VERIFY PASS, 219 modules (204 listed + 15 dependencies),
  1,704 audited theorems, 0 sorry, 0 native_decide, axioms within {propext, Classical.choice,
  Quot.sound}. `full8_20260926` was started and did not finish (later modules `notbuilt`).
- Since full7: smoke gates C1–C4, B1, B2 (26 Sep) all SMOKE PASS. smokeB2_20260926: 45 modules,
  352 theorems, DRIFT empty.
- Roster subagents (a0db, a703, a72b, ac26, a921) were asked for takeover reports; the user stopped
  all five before any report was written. Takeover is from their PROGRESS files and the Lean itself.
- Statement extraction used for this reading: `scratchpad/audit27/stmts_<group>.txt`.

## 1. Paper C Lean (97 modules)

### 1.1 The C objective and its generic tools (read: Attain, Band, BandValueBridge, BaselineAttain, Break3, Breakpoint, BudgetAware, BudgetExchange, BudgetExchangeOdd, BudgetFamilies, BudgetGm, BudgetSharp, BudgetSym, Collapse*, CountRecourse, CountReduction head)

- **The objective is a signed-sum balancing objective.** `subCost g k S` is the normalised regret of a
  k-set S for a weight vector g: `(|Σ_{i∈S} g_i| − trueBaseline g k)/normMass g`. Every C theorem is
  about this objective, a marginal "exposure" band `|Pr(i ∈ prefix_k) − k/m| ≤ η/m`, and a budget set K.
- **Generic in g (any real weight vector), not generic in the set function.** `LeanPaperCBudgetAwareV1`
  defines the three values used by the MARL memo, all for this objective:
  `trueValue` (one ranking law for all budgets, U), `awareValue` (per-budget subset laws, B),
  `recourseValue R` (commit a ranking law, then at budget k edit the prefix by ≤ R exchanges, V^(R)).
  Proved for all g: `aware_le_recourse`, `recourse_le_true`, `recourse_zero` (V^(0)=U),
  `recourse_mono`, `recourse_full` (V^(R)=B once R ≥ min(k, m−k) for all k ∈ K),
  `linear_lower`/`layer_ge_of_linear` (LP-dual certificate for B), `aware_le_true`.
  The definitions take `subCost g`; the proofs of the order relations use only that subCost is a
  function of the final set, so re-parameterising by an arbitrary set loss ℓ(S) is mechanical
  but NOT done. The type/count reductions (`CountReductionV1`, `CountRecourseV1`,
  `recourse_eq_count`) need a type labelling under which the loss is invariant.
- **Commitment price and one-exchange results that exist (all on this objective):**
  - four-item family g=(a,−a,b,−b): `aware_twoMag`, `advantage_*` (U−B = 0 on η≤1/3, positive
    after), `recourse_one_twoMag` (V^(1)=B for all η), `recourse_zero_twoMag`, `exchange_needed`
    (V^(1)<V^(0) iff η>1/3). This is a complete, gated "price of commitment + one exchange closes
    it" statement.
  - g_m family: `aware_even_exact`, `aware_odd_exact`, `advantage_even_pos_iff`,
    `advantage_odd_pos_iff` (sharp zero-value ranges), `recourse_eq_aware_even/odd` (on those
    ranges every R), `recourse_one_even` (even m ≥ 4, every η: V^(1)=B).
  - **Odd m one exchange (`LeanPaperCBudgetExchangeOddV1`, 726 lines): headline
    `recourse_one_odd` is ABSENT.** Present: the committed law `oddLaw` with band 0
    (`oddLaw_feasible`), the one-exchange edit `oddT` with `oddT_card`, `oddT_sdiff` (≤1 exchange),
    `oddT_gsum`, `oddT_cost = 0` at middle budgets. Missing: the band of the edited final law
    (`oddT_band`), the end budgets 1 and m−1, and the assembly into `recourse_one_odd`. Not in
    MODS, not gated. Estimated 70–75% (cost and exchange count done; band and assembly left).
- **Collapse/robustness** (CollapseV1, CollapseScaleV1, CollapseWindowV1): price ratio
  Θ(min(m, 1/ε)) under ℓ1 perturbation ε of g_m, satisfiability witness present. g_m-specific.
- **Breakpoint** (BreakpointV1, BandV1, Break3V1, BandValueBridgeV1): symmetrisation, the
  marginal bridge, layered flow → ranking law (`pathDecomposition_discharged`), path/trajectory
  laws. The flow → ranking realisation is generic (any layered flow on count states).

### 1.2 The rest of C (all 97 modules read: module docs + every theorem name; full statements for the generic modules)

What C proves, grouped by how general it is:

| Level | Content | Key modules / theorems |
|---|---|---|
| Any finite law, any observables | ranking law → flow on prefix states is marginalisation; objective and whole budget vector transport | `FlowV1` (`sum_joint_*`), `NamingV1`, `TransportV1` (`vector_transports`, `band_transports` under an explicit type-interchangeability hypothesis) |
| Any typed multiset g = wt∘ty, any cost on count states | ranking laws ⇔ band-feasible count flows, same achievable budget-cost VECTORS (`banded_vectors_agree`, `typed_flow_equivalence`, `infima_agree`); dual certificates by potentials (`cert_lower`); primal certificates by mixtures of type sequences (`mixFlow_*`); free threshold `etaFree` attained, `free_threshold`, `gap_stable` (6·ℓ1/d) | `FlowLawV1`, `FlowBandJoinV1`, `TypedFlowV1`, `FlowCertV1`, `PathMixV1`, `FreeBandV1` |
| Any weight vector g | value stability `|V(g)−V(g')| ≤ 3‖g−g'‖₁/d`; convexity/antitone in η; strict gap from compactness; budget-aware B, recourse V^(R) and their order relations; count model of recourse = item model (`recourse_eq_count`, both directions) | `StabilityEndgameV1`, `FrontierV1`, `FinalV1`, `BudgetAwareV1`, `CountReductionV1`, `CountRecourseV1` |
| Specific families | g_m: full even frontier, full odd frontier (two lines, kink law), ex-post value 2/(m+4) (factor m−1 over ex ante), collapse Θ(min(m,1/ε)), robust ball; g4, (1,1,2,2), (2,2,1,1), (2,2,2,2): exact frontiers at every ratio and band, price laws with irrational breakpoints 5−2√2, 7−2√6; budget-aware exact values, sharp zero-advantage ranges; one exchange suffices for g4 and even g_m | the remaining ~70 modules |

Audit trail visible in the Lean (these are good signs, not defects): `VacuityV1` proves the original
flow domain `CountFeasible` was EMPTY (so the first reduction was vacuous) and `HorizonV1`/`HorizonSecV1`
repair it with an inhabited domain; `EvenResolveV1` retracts a wrong contradiction note;
`LowerZeroV1` retracts an "exact" over-claim; several modules state "conditional assembly, not a
closed headline" until a later module supplies the data. `FamilyV1` proves the predicates do not pin
the family (`isEvenFamily_not_forcing_two_heavy`).

**What C does not have, relevant to the MARL proposal.**
1. No theorem for an arbitrary set function ℓ(S). Everything is |signed sum| minus the per-budget
   optimum. The flow machinery works for any count-state cost, so an arbitrary ℓ needs singleton
   types (d = m, count states = subsets, 2^m states); that instantiation is not written.
2. No non-nestedness characterisation. The price of commitment is computed family by family.
3. No bound of the form "R exchanges recover a fraction f(R) of the price". What exists is: V^(0)=U,
   V^(R) monotone, V^(R)=B once R ≥ min(k,m−k), and V^(1)=B on g4 and even g_m (odd g_m 70–75%).
4. The exposure band η is structural in every C theorem. Its MARL reading (a fairness/starvation
   floor on how often each neighbour is heard) must be justified or set to the vacuous η = m.
   At η = m, B equals the per-budget optimum and U is the plain "one ranking for all budgets" value.

## 2. Structural Lean (49 modules, all read)

The structural objective is the support-radius loss `selectedRadius f S = supportOsc(Sᶜ, f)/2`
for components f : ι → Ω → ℝ (the worst oscillation, over support worlds, of the omitted
components); `SupportOscMaxModularV1` proves it is a maximum of modular scenario functions.
This is a loss of dropping components (interactions) — not a signed-sum balancing loss.

**Generic results (any finite instance of this class):**
- Prefix-cover dimension χ_ε = least number of full rankings whose prefixes hit an ε-optimal set at
  every budget. Proved equivalent to a ranking-free chain-cover of the layered ε-optimal poset
  (`prefixCoverDimensionAtMost_iff_layerTransversal_inclusionChainCover`,
  `S3_prefix_dimension_iff_minimum_transversal_prefix_width`); χ=1 iff a nested optimal chain
  exists (`STRUCT_B2_chi_one_iff_nested_optimal_chain`).
- Universal upper χ ≤ |I|+1; at fixed normalised tolerance ε, χ_ε ≤ ⌊2/ε⌋+1 with no dependence on
  sizes (`normalized_dimension_le`); quantifier order pinned (`quantifier_order_not_interchangeable`).
- **One ranking is (2/3)-optimal at every budget**, for every instance: delete a minimum-span
  element repeatedly (`SortedPrefixV1.one_prefix_chain`, `RecourseUniformNestingV1.excess_le_two_thirds`).
  So the normalised price of commitment is at most 2/3 in this class.
- Ordered-radius / approximate-anchor chains: one ranking from any (approximate) budget anchor with
  error control at all later budgets (`anchored_ranking`, `approximate_anchored_ranking`,
  `approximate_menu`); budget nets (`budget_net_cover`) "without monotonicity or submodularity".
- Ex-ante vs ex-post (`AvgPathGapV1`): avgVal ≤ pathVal ≤ b·avgVal, attained (`gap_exactly_card`),
  mechanism in `SaturationV1`; robust separation under relaxed marginals (`RobustSeparationV1`).
- Randomised menus: `random_menu_exact`, `post_randomization_adversary`.
- `BudgetRecourseV1`: `selected_difference`, `deletion_card`, `transition_law`,
  `good_decision_forced`, `policy_total` — deletions forced between budget-optimal selections.

**Families/witnesses:** staircase family with unbounded χ (`STRUCT_UNBOUNDED_*`), exact χ = r
(`STRUCT_staircase_prefix_dimension_eq`), full tolerance curve (`exact_curve`), but one ranking is
within 1/(2r) after normalisation (`one_ranking_normalized`) — exact complexity is not robust.
χ ≥ 3, ≥ 4, ≥ 5 witnesses; the native_decide versions are superseded by kernel `decide` rewrites
(`*KernelV1`); the native_decide originals remain in the tree but are not in the audited set.
`AllOptimalExtensionConjecture` is quarantined with an explicit counterexample.

**Consequence for the MARL proposal.** The "price of committing to one ranking before the budget is
known" is ALREADY the structural paper's central object, in a loss class (support radius = worst
omitted-component oscillation) that is a natural model of "dropping interaction information".
Structural gives what C lacks: generic upper bounds (2/3, ⌊2/ε⌋+1), unbounded-complexity lower
families, and ex-ante/ex-post gaps. C adds: the fairness band, exact values, recourse. A MARL T1 should
be built on structural's class and theorems, with C's recourse layer, not on C's signed sums.

## 3. Support Lean (38 modules) and Query Lean (21 modules), all read

**Support** (decision-critical support identification in the same support-radius geometry):
fibre-safety is the exact condition for a universally safe controller and pairwise separation is
NOT sufficient (`pairwise_separation_not_sufficient`, realised in the real geometry by
`ThreeWorldWitnessV1.pairwise_not_sufficient_in_support_model`); obstruction order determines neither
the upper nor the lower query cost (`obstruction_order_determines_neither_bound`,
`UnboundedObstructionV1.one_query_sound`); exact adaptive/nonadaptive membership-query laws;
passive sampling: decide-safely rate Θ((1−Σp_i)^N) vs recover-all rate Θ((1−min p_i)^N)
(`recovery_sandwich`, `decide_*_expect`, `growing_K_recover`); Bayes = minimax with a constructed
equivariant decoder (`bayes_minimax`, `passive_minimax`, `equivariant_is_minimax`); parity bundle size
(`parity_bundle_insufficient`, `greedy_ratio_unbounded`, citing Krause–Guestrin 2005 XOR);
reduction of the multi-tip geometry to a general finite decision-region problem with the same query
cost (`GeometryReductionV1.cost_preserving`) — so the geometry is not more general than decision
regions, and the module says so.

**Query** (information depends on the query/channel class):
- The finite-Gaussian-mixture analytic chain is COMPLETE in Lean: level cancellation and
  non-vanishing of the order-r coefficient (`levelSum_ne_zero`, `mixture_coeff_ne_zero`),
  integrable Gaussian envelope (`envelope_integrable`), uniform Taylor remainder
  (`hellinger_upper_const`), interval lower bound (`hellinger_lower_from_interval`), convergence of
  H²/h^{2r} to (1/8)∫Δ_r²/p₀ > 0 (`hellinger_ratio_tendsto`, `limit_pos_of_ae_ne_zero`), then
  tensorisation and the integer sample count (`iid_testing_bracket`, `matching_rate`,
  `rate_two_sided`), and the regret bridge γ·e ≤ R ≤ L_max·e (`bayes_regret_window`).
- Pairwise-response insufficiency and an XOR synergy witness (`E4_xor_synergy_witness`,
  `E3_pairwise_response_not_sufficient_for_interaction`); representation necessity (QN1–QN4);
  randomised vs deterministic minimax floor (`deterministic_minimax_is_larger`).

**Finding (B crossover, important).** The other assistant's B step 3 ("actual density expansion →
nonzero coefficient → integrable envelope → uniform remainder → two-sided Hellinger") is, for a
FIXED probe parameter, exactly the Query chain above, already proved for any finite Gaussian mixture
p_{W,h}(y) = Σ_x π_x φ_σ(y − f_W(x) − h g(x)). What is genuinely missing for B's transition claim is
(a) checking that B's crossover probe has this finite-mixture form, (b) uniformity in the second
parameter η (joint (h, η) remainder), and (c) the whole-class upper bound. (a) must be checked
against `LeanPaperBCrossoverV1` / `famLaw` (§4).

## 4. Paper B Lean (77 modules, all read)

**General laws (any finite worlds/answers/safe correspondence, any channel in protocol form):**
obstruction law lower side for finite-horizon and for a.s.-stopping adaptive randomised policies
(`obstruction_lower`, `obstruction_lower_chi`, `stopped_obstruction_lower*`); χ² star law without the
1/(|W|−1) factor (`chi_star_lower`), and a certificate channel showing that factor is necessary for
KL (`cert_tight`); upper side by Hellinger tournament (`hellinger_tournament`, |W|² blocks) and by a
sharing tournament (`share_tournament`, |Q| blocks), with `private_query_lower` showing |Q| cannot be
removed; per-world decision order `dOrder` with two-sided law `decision_order_visible`; critical
game G* with generic limit `critical_limit`, `private_game`, `shared_game`, `same_order_ratio`;
query design ⇔ hitting set (`hitting_embeds`, `id_iff_hitting`; NP-hardness cited, not formalised).
Continuous-alphabet change of measure on a filtration (`change_of_measure`, `kl_eq_sum_increments`),
policy cancellation (`policy_contributes_nothing`).

**Instances:** parity channel — safe rate log(1/δ)/h², identification log(1/δ)/h^{2(m−1)} on the same
experiment (`parity_tip_finish`, `stopped_parity_rates`), per-world law (`parity_world_law`);
latent family F_{u,v}(z)=3u z₁−2z₂−2z₃+v χ_r(z_tail), Y=F+h g(Z)+ξ — both minimax rates
(`family_safe_minimax`, `family_id_minimax`, stopped versions), safe sets derived from the loss
(`famSafe_derived`), decision moment and tail moment laws on the observation law
(`decision_second_moment_famLaw`, `tail_moment_gap`).

**Honesty trail in the Lean:** `WorldsV1.self_difference_not_a_density` shows the old `hdiff`
composition was vacuous at h ≠ 0; `ScopeV1` narrows that retraction to first order;
`ExactConstV1` shows the loosened constant goes negative at K=4, δ=0.05 and replaces it;
`ChiIntegrableV1` closes the Bochner "non-integrable integrates to 0" gap; `DecoderMatchV1`
compares the Lean decoder with the Python one.

**Incomplete modules (not in MODS, not gated):**
- `LeanPaperBParityCriticalV1` (666 lines): leading-order expansions and limits of the per-query
  χ² and KL of the parity channel are proved (`chi_limit`, `kl_limit`, `lead_limit_pos`,
  `cj_pos`); the assembly `parity_critical_game` (the game value G* of the parity channel) is
  absent. Estimated 80%: remaining is composing `critical_limit` with `cj`.
- `LeanPaperBCrossoverV1` (150 lines): exact moments, odd/even cross-term cancellation, the
  algebraic shape h⁶+η²h⁴ (`two_scale_shape`). No density, no Hellinger. Estimated 20%.
- `ChiIntegrableV1`, `TailMomentV1`: complete, not yet in MODS.

**Cross-check of the crossover gap against Query (§3).** B's latent family law `famLaw` is a finite
Gaussian mixture over the 8·2^r latent patterns with mean F_{u,v}(z)+h g(z). That is exactly the
form of Query's analytic chain (p_{W,h}(y)=Σ_x π_x φ_σ(y−f_W(x)−h g(x))). So at each FIXED η the
two-sided H² ≍ h^{2r(η)} with explicit limit constant is an instantiation of existing Query
theorems once the level condition for g_η is checked (r(0)=3, r(η>0)=2 per `CrossoverV1`). The new
math is only the joint uniformity in (h, η) and the widened-class upper bound, and the latter may
follow from `LeanUnifiedQueryOrderV1` (degree-d probes cannot see a degree-n character before order
⌈n/d⌉) — to be checked in §8. The other assistant's plan to build the analytic chain from scratch
would duplicate proved work.

## 5. Functional Lean (36 modules, all read)

Top-K / range "capacity" of relations with Gaussian cell responses: game information
J(w) = min over answer-flipping alternatives of the weighted energy; exact values on crossover
families (`crossover_sandwich_sharp`, `heterogeneous_upper`, `energyU_ge_pairV`), effective-resistance
law for edge-contrast designs (`pair_infimum_exact`, harmonic potential gives both certificates),
KKT certificate without a matrix inverse (`kkt_certificate`), concavity of J and an exact witness that
the closed-form allocation is NOT optimal (`wstar_not_optimal`), the alternative set is a finite
union of convex pair regions (`alternative_union_polyhedra`), and the scalar proxy is wrong in both
directions by no constant (`scalar_not_upper_to_any_constant`, `scalar_not_lower_to_any_constant`).

**MARL-relevant and so far unused:** `CertificateLifetimeV1` (LIFE1–LIFE5: a Top-K certificate stays
valid while accumulated policy drift is below its margin; `LIFE4_within_certified_lifetime`,
`LIFE5_future_topK_margin`), `SelectiveMaintenanceV1` and `ResidualMaintenanceV2` (which certificates
to refresh after drift; minimum-cost refresh set exists and is safe; dependency locality). This is a
proved "when does a stale interaction ranking stop being valid" layer — exactly the moving-traffic
staleness question the MARL memo leaves to experiments.

## 6. D6 Lean (261 modules, all read at doc + theorem-name level)

Object: product-reference compression. A world F on a product action space, a product reference q,
first-order responses (`productResponse`), the retained residual, the compression loss ℓ_S of
retaining coordinate set S, the Top-C rule (keep the C coordinates of largest response span — a
NESTED rule, i.e. the prefixes of one score ranking), and the interaction strength δ□ = max mixed
difference (four-atom cycle functional).

**Proved (general in F, q):**
- `SmallSymmetricDifference.pair_loss_le_sdiff_card`: ℓ_S − ℓ_T ≤ |S \ T|·δ□ for equal-size S, T.
  Hence 2D ≤ 2 min(k, m−k) δ□; sharp at m = 6 (`SharpnessM6V1.six_optimal_at_m6`,
  `M6SharpnessBridgeV1.chain_constant_six_sharp`).
- `SharpMarginThresholdV1.margin_two_sufficient`: if the Top-C score margin is ≥ 2δ□, Top-C is
  decision-optimal (degenerate references allowed); `every_subthreshold_margin_fails`: matching
  witnesses at every margin in [1, 2).
- First-order responses are insufficient in general (`D6_B7_first_order_response_only_not_universally_exact`,
  `..._no_finset_singleton_controller_universally_zero_regret`).
- Reference phase law: buying reference evidence (t > 0) strictly lowers the decision-insufficiency
  threshold ρ* = 2a − e/k (`threshold_strictly_below_corner`, `phase_value_zero_iff`,
  `physical_minimax_certificates`).
- Rank-one interaction structure: characterisations (minors, affine slices, multiaffine normal
  form, reference invariance).
- An allocation/acquisition programme (oracle allocation games with sharp saddle values, discovery
  with stopping, confidence sequences, epoch composition — `weighted_epoch_total`,
  `multi_epoch_total` — revalidation). These are oracle-design or one-epoch statements; each module
  says which stopping/rate claims are NOT made.

**Refuted (exact counterexamples in Lean):** the universal (m−1)δ□ half-factor law, in the
unnormalised, normalised, ternary, strict-margin, rank-one and two-profile versions
(`BalancedLawCounterexampleV1`, `NormalizedBalancedTernaryCounterexampleV1`,
`StrictMarginTernaryCounterexampleV1`, `StrictTwoProfileRankOneM6CounterexampleV2`,
`BinaryIntegerCounterexampleV1`), plus the proposed proof routes BEX, DBEX, pair contraction,
canonical Abel. The original conjecture module is quarantined. The native_decide uses in
`PairContractionCounterexample` are superseded by kernel versions.

**Consequence for the MARL proposal (major).** D6 already contains the loss bridge the MARL memo's
T1/T2 needs, in a far better form than the XOR toy:
1. Top-C by response span is a universal (nested) ranking. `margin_two_sufficient` is a sufficient
   condition for it to be optimal at every budget: no commitment price when the score margin
   dominates twice the interaction strength.
2. `pair_loss_le_sdiff_card` bounds the loss gap between ANY two retained sets by
   (number of differing items)·δ□. So after R replacements toward the budget-optimal set T, the
   residual gap is at most (|prefix \ T| − R)·δ□ whenever the intermediate sets are legal — a
   quantitative "limited revision" bound, linear in the remaining distance and in the interaction.
3. The (m−1) refutations show the interaction constant cannot be improved to m−1 in general; the
   sharp constant at m=6 is 6.
Missing: the statement for the prefix-vs-budget-optimum pair, and the recourse monotonicity along
exchange paths (each exchange step is a symmetric-difference-2 move, so the bound applies per step).

## 7. Paper A Lean (91 modules, all read at doc + theorem-name level)

Object: adaptive measurement for a compression decision (retain arm A or B by comparing ranges),
Gaussian cells, Track-and-Stop-style learners. Proved: the frozen-linear surrogate misprices after
optimising the design, in both directions, with no constant factor (`no_constant_factor_after_sup`,
`rpair_ratio_le` at unit variance); every surrogate-optimal design starves the decision-relevant
middle cells (`starvation_at_optimum`, `starvation_at`); the ideal learner attains the true game
rate log(1/δ)/Γ (`ideal_upper_rate`, `ideal_family_finish`) and is δ-correct; surrogate-following
learners (fixed design, and re-solved at the estimate) pay Ω(log²(1/δ)) (`starved_cost_log_sq`,
`est_cost_log_sq`); repair frontier R(b) (concave, continuous, exact slope at 0), budget law
E N ≥ D_δ/R(b) on nested policy classes, attained by a tracking learner (`budget_law`,
`frontier_rate_lower`, `optimal_lower`/`optimal_upper` on Gaussian cells), stopped versions without
positivity (`RepairNoPosV1`), sacrifice duality with certificate pairs (`SacrificeDualityV1`), and the
full probability plumbing (Ville on the actual stream, freezing lemma, GLR measurability, layer-cake
on ℕ∞). The honesty trail: `TwoSurrogatesV1` separates two objects the manuscript had named the
same; `ThresholdV1` shows the code's threshold is unbounded and repairs the chain;
`AFrozenV1.proxyAlt_ne_frozenAlt` refutes an assumed set equality.

A's MARL relevance is limited to the case where interaction measurement is itself a paid,
learned quantity (the memo's route 3): "a surrogate importance score used to decide what to measure
starves exactly the interactions the decision turns on" is a proved, transferable warning for
learned attention/critic scores. It is not needed for the core commitment/recourse story.

## 8. Unified, Master, Adaptive, Other, AxiomAudit (all read)

- **Unified.** `LeanUnifiedQueryOrderV1`: a measurement of degree ≤ d of a latent sign vector sees the
  degree-n top character first at moment order s = ⌈n/d⌉, and this is attained
  (`moment_vanishes_below_s`, `top_query_is_informative_at_first_order`). For B's crossover this
  gives the whole-class ORDER statement (linear probes on a 3-coordinate tail: s=3 → h⁶; degree-2
  probes: s=2 → h⁴) at the moment level; the whole-class Hellinger UPPER bound for degree-2 probes
  is still new work (B's `chi2_uniform` is for linear shifts). `LeanUnifiedSupportExchangeV1`:
  restricting the loss to a deployment support K can make Top-C non-optimal even with zero
  interaction (δ_I = 0), with an explicit geometry term (`witness_topC_not_optimal_on_support`,
  `support_optimal_of_margin`). `LeanUnifiedObstructionOrderV1`: classes resolve iff no obstruction
  lies inside a class; randomised error floors. `LeanUnifiedStructuralRelaxedV1`: the band lower
  bound (m+3−(m+1)η)/(m(m+4)).
- **Master.** Calibration (anchor) queries: anchor-free vs anchored values with separated
  certificates, exact critical price c* = (m−1)²/(m+3)², full-class calibration law (a group with
  no calibration query has Γ = 0), rank-one nuisance gives no complementarity, rank two does.
- **Adaptive.** Tracking exists per horizon but the online largest-deficit rule cannot keep deficit
  below 1 (`online_quota_fails`, kernel-computed trajectory); doubling-epoch loop with revalidation
  (`stop_sound`, `late_revalidation_can_overshoot`); layer-cake and finiteness from tails.
- **Other.** Product mixed-difference core (`D6_product_topC_compression_decision_regret`), typed
  certificate completion with five irreducible obstruction types and a direct-product
  indispensability calculus, binary Pinsker, finite trackers, Gaussian overlap risks, minimax-risk
  bridge to Mathlib's `minimaxRisk`.
- **Sorry / native_decide.** Outside comments, `sorry` appears only in the quarantined
  `LeanD6DecisionHalfFactorConjecture`. `native_decide` appears in older witness modules whose
  kernel-`decide` replacements exist (`*KernelV1`); those originals are not in the audited set.

## 9. Compiled-state finding: the seven older papers have no from-scratch gate

The frozen, from-scratch gate (`verify_all.sh`, in use since 2026-09-23) has built 278 distinct
modules across all runs. Every module cited by papers A, B, C is among them (64/64, 52/52, 76/76).
For the seven older manuscripts the counts of cited modules that were ever gated are:
master 0/7, functional 0/21, support 1/35, query 0/13, structural 0/13, adaptive 0/8, d6 0/51,
unified 3/7. The local `.lake` holds no olean for almost all of them (e.g. structural 0/13 present,
d6 1/51). Their earlier verification used the pre-2026-09-23 runner, which the gate script's own
header says could reuse stale oleans and never rebuilt old dependencies. So the older papers'
Lean claims are currently unverified under the present toolchain — a provenance gap, not a
known error. Any MARL paper that reuses Structural or D6 theorems must first gate those modules.

## 10. Plans, earlier audits and MARL code assets (read)

- `audits/BC_TRAFFIC_EXECUTION_AND_STORY_AUDIT_20260926.md` (other assistant): C as commitment to a
  nested inference configuration under unknown compute budget on trained traffic forecasters
  (METR-LA/PEMS-BAY), generic-cost instantiation of C's flow theorems via singleton types, B's
  MetaDrive proposal audited (universal WAIT trivialises, generic Gaussian noise gives order 1,
  t* is not an exact sample count). §19 restores the MARL goal. This plan is sound; its C part is a
  compression/forecasting plan, not a MARL paper.
- `audits/PAPER_C_FINAL_NOVELTY_REVIEW_20260926.md`: closest priors for C at statement level —
  Storandt–Funke 2019 (regret-minimising permutations over prefixes), Singh–Kempe–Joachims 2021
  (all-prefix marginal constraints), Bienkowski et al. 2026 (incremental maximisation, ratio ≈1.373
  for monotone submodular, lower bound 1.25), Koike–Lin–Wang (joint mixability), Bellini et al.
  2016, prefix discrepancy/Steinitz, Chassein et al. (recoverable selection: choose p items, swap
  ≤ k after the scenario is revealed), Hommelsheim et al. 2026, Nasrabadi–Orlin 2013,
  Mastin–Jaillet–Chin. Verdict there: C's exact laws are defensible; generic "one ordering for all
  budgets", "limited exchange after reveal" and "randomised minimax regret" are NOT new.
- `audits/BC_PROGRESS_AND_RESULT_AUDIT_20260926_LATE.md`: confirms B gates and the two incomplete
  headers (ParityCritical, BudgetExchangeOdd) found independently in §1 and §4 here; notes
  paper_b.tex lines 580–588 still call the decision moment a by-hand certificate although
  `DecisionMomentV1` is gated.
- **Original MARL line (historical, important):** `models/kprefix_net.py` is a Plackett–Luce
  network that outputs a MENU of K full rankings ("K-Prefix Incremental Optimisation"); a ranking is
  nested by construction. `research/kprefix/benchmark.json` is a tier-A exact finite benchmark
  (m=5, 6 train / 4 test instances, K ∈ {1,2,3}, `development_only: true`,
  `policy_return_status: DEFERRED_TO_TIER_B_C_MARL_ADAPTERS`). So the structural paper's prefix-cover
  dimension χ (menu of K rankings) was the original MARL design object; the learned MARL tiers were
  never run. `research/new_chains_v2/*`: MARL runners executed only as plumbing smoke; learned-MARL
  adapters PARTIAL; F3 moving-estimand adapter NOT IMPLEMENTED.
- **External MARL environments already integrated:** `envs/external/{cityflow,rware,cyborg}.py`,
  `flatland_adapter.py`, `omni_arena.py`, with pinned repos in `external_envs/repos/`
  (CityFlow, CybORG, flatland-rl, robotic-warehouse) and an isolated runtime.
  `ADAPTER_CAPABILITY_MATRIX.md` rates CityFlow (multi-intersection traffic signal control) as the
  most promising external environment (clone, phase masks, applied-phase receipt; learned-policy
  hook missing). A moving-traffic MARL experiment can start from CityFlow rather than from a new
  MetaDrive/SUMO integration.

## 11. Literature check for the MARL direction (primary sources opened this pass)

| Prior work | What it already has | Consequence |
|---|---|---|
| Bernstein–Disser–Groß–Himburg, Math. Prog. 2022 (arXiv 1705.10253) | one ordering good for all cardinalities; 2.618-competitive for a broad monotone class, lower bound 2.18 | "committing one ranking across unknown budgets has a price" is classical |
| Bienkowski et al., arXiv 2606.28558 (Jun 2026) | incremental submodular: greedy e/(e−1), new 1.373, lower bound 1.25 | same object, submodular value |
| Incremental–decremental maximisation, arXiv 2508.14516 | ordering while replacing elements, curvature / submodularity-ratio classes | a recourse-like variant exists |
| Recoverable robust cardinality-constrained maximisation with commitment, Acta Informatica 2026 | commit a set, deletions revealed, bounded replacement | "limited revision after reveal" exists for submodular value |
| Chassein et al. 2017 (1701.06064); k-delete recoverable robust 0–1 (2609.29478) | choose p items, exchange ≤ k after the scenario | same |
| Dynamic consistent submodular maximisation, arXiv 2606.04946 | bounded recourse per update, 1/2−ε with O(1/ε²) changes | "few changes per step" exists in dynamic form |
| Where2comm, NeurIPS 2022 | ONE model serves varying bandwidth by truncating a confidence-priority map | this is exactly the universal-ranking (R=0) policy, in V2X perception |
| SchedNet, IMAC, NDQ, ETCNet, CASEC, SOP-CG, MUTE, CoLight | priority scheduling, bandwidth-limited messages, decision-preserving graph pruning, neighbour attention in traffic signal control | selecting important neighbours/messages is not new |
| SLIM (arXiv 2605.21085), IB+VQ (2602.02035), priority-driven control and communication (2605.10482, IFAC 2026) | normalised bandwidth budget, many budget levels, learned priorities | recent and close; none found with non-nested budget optima + bounded revision theory |

Not found in these sources: a price of commitment and a revision frontier parameterised by an
INTERACTION strength (mixed differences) against a score margin, with sharp constants; randomised
ranking laws under exposure bands; the menu-versus-revision trade-off; an ex-ante/ex-post budget
timing law; any of these for a team decision loss inside a learned MARL controller. The search was
targeted, not exhaustive. Liu–Wang 2026 (named in the other session) could not be identified from
the repository or transcript: it is in no bibliography; its title is needed to fetch it.

## 12. Verdict: is the proposed MARL direction the most novel version achievable?

**The direction is right; the proposed T1 is its weakest part.** "A ranking committed before the
budget is known has a price, and R replacements reduce it" is, as a generic statement, incremental
maximisation plus recoverable robustness (§11). The XOR three-message game is a clean instance of
complementarity, which the literature already treats (non-submodular value of information,
Krause–Guestrin XOR; the corpus itself cites it in `SupportParityBundleSizeV1`).

**A stronger, still achievable T1 uses results that are already proved in this corpus and that
the MARL memo under-uses:**

1. **Zero-price regime (from D6).** `margin_two_sufficient`: if every consecutive score gap of the
   response-span ranking is at least 2δ□, the score ranking (nested by construction) is optimal at
   every budget, so universal = budget-aware and no revision is needed. Corollary to state:
   an all-cuts version of the per-k theorem.
2. **Price of the score ranking (from D6), and what is still missing for revision.**
   `pair_loss_le_sdiff_card` (and its score-surplus and margin forms) require the `selected` set to be
   Top-k by response span — i.e. a prefix of the score ranking. So for the universal score ranking
   the commitment price at budget k is at most |prefix_k \ T_k|·δ□ ≤ min(k, m−k)·δ□ (direct corollary),
   minus a score-surplus term (`pair_loss_le_sdiff_card_sub_score_surplus`). Sharpness: the m = 6
   constant 6 = 2·min(k,m−k) is attained (`six_optimal_at_m6`); the (m−1) law is refuted in every
   tested variant. **A revision frontier (d_k − R)_+·δ□ is NOT a corollary**: after one exchange
   the set is no longer Top-k, so the lemma's hypothesis fails. It needs a new lemma for an
   arbitrary retained set (loss gap ≤ distance·δ□ plus a score-deficit term), which the existing
   proof pieces (`retainedResidual_sdiff_identity`, `directed_response_sum_le_spans`) make plausible
   but do not give. This is the central new theorem to attempt.
3. **Support restriction breaks nesting even without interaction** (`UnifiedSupportExchangeV1`):
   on a deployment support K, Top-C can be non-optimal with δ_I = 0. In traffic, the reachable
   joint-state support is exactly such a restriction.
4. **Menu versus revision (from Structural + C).** Two ways to pay for non-nestedness: store K
   rankings (prefix-cover dimension χ; the original KPrefixNet design) or revise R items after the
   reveal. Proved ingredients: χ_ε ≤ ⌊2/ε⌋+1 for every instance, one ranking is 2/3-optimal at every
   budget, χ can be unbounded, V^(R) = B once R ≥ min(k, m−k). A theorem relating K and R is new work
   and would connect the paper to the project's original MARL architecture.
5. **Timing law (from Structural + C).** If the budget can depend on the realised ranking or state
   (bandwidth drops when traffic is dense), the relevant objective is E max_k, and the gap to
   max_k E is at most the number of budgets and attained (`gap_exactly_card`, `path_over_free`).
6. **Staleness layer for moving traffic (from Functional).** Certificate lifetime under bounded drift
   and minimum-cost selective refresh (`LIFE4_within_certified_lifetime`,
   `LIFE_B3_minimum_refresh_is_safe`) give a proved rule for how long a committed ranking stays
   valid and what to refresh — revision in time rather than across budgets.
7. **Decision sufficiency (from B + Support).** Stop acquiring when the surviving worlds share a
   common joint action; pairwise compatibility is provably insufficient in the real geometry.

Items 1–2 turn the paper's empirical claim into a falsifiable PREDICTION: revision should help
exactly where the measured ratio of interaction strength (mixed differences of the critic) to
score margin is large, and nowhere else. That also protects against the risk the memo names (a
simple budget-conditioned selector matching the method): the theory says when that must happen.

**Environment.** CityFlow is already integrated (`envs/external/cityflow.py`, pinned repo,
isolated runtime; rated most promising in `ADAPTER_CAPABILITY_MATRIX.md`). Multi-intersection
signal control is moving traffic with learned agents, neighbour messages are natural, and CoLight's
neighbour attention is the natural universal-ranking baseline. MetaDrive needs a new integration;
use it second, for vehicle-level coordination.

**Before any MARL manuscript text:** gate Structural, D6 and Functional modules from scratch (§9);
write the generic-cost recourse wrapper (singleton types) the other session specified; formalise
items 1–2 as corollaries (short, from existing D6 lemmas); keep the XOR game as the smallest
witness, formalised.

## 13. B and C items found in this pass (unchanged, for the record)

- paper_b_supplement.tex lines 398–399: "the crossover therefore sits at η≍h: a nonlinear
  measurement capability of order h already erases the advantage" — wrong as a statement about
  the exponent: with H² ≍ c₆h⁶ + c₄η²h⁴, η = ch gives (c₆+c₄c²)h⁶. Confirmed.
- paper_b.tex line 583 still says the decision second moment is "computed by hand \CERT";
  `LeanPaperBDecisionMomentV1` is gated (smokeB2_20260926 PASS). The prepared `apply_B2.py`
  covers this; it was not run in this pass.
- structural.tex line 480: "a further $0$ audited declarations" — template residue.
- Incomplete, not gated: `LeanPaperCBudgetExchangeOddV1` (≈70–75%), `LeanPaperBParityCriticalV1`
  (≈80%), `LeanPaperBCrossoverV1` (algebra only; the analytic part can reuse the Query chain).
  Complete but not in MODS: `LeanPaperBChiIntegrableV1`, `LeanPaperBTailMomentV1`.
## 14. Cross-check of `MARL_PRIOR_ART_RECOURSE_AND_A_ROLE_20260927.md` (other session)

- Prior art: consistent with §11 and adds unknown-capacity knapsack (SIAM 2017), Hommelsheim et al.
  2026, Münch et al. (Acta Informatica 2026, predecessor IWOCA 2025), MBDP (ICC Workshops 2025),
  BAMAS (AAAI 2026), "Don't Fire Together" (Sensors 2026: frozen learned policy + communication
  scheduling + staleness — collides with a generic staleness claim; §12 item 6 must be positioned
  as a proved validity rule, not as staleness-aware scheduling).
- Its correction is right: `paper_c.tex` lines 204–250 already cite and distinguish incremental
  maximisation (disser2023, bienkowski2026), Storandt–Funke, recoverable selection (chassein2017),
  commitment under deletions (hommelsheim2026) and online discrepancy (gupta2022).
- R* = min_π max_k min_{S∈O_k} d(P_k(π), S): correct as the exact-recovery threshold; the memo
  itself notes it misses the randomised frontier (V_det(0)=1/4, V_rand(0)=1/8 at p=1/4). C's
  `trueValue`/`recourseValue` are already randomised over ranking laws, so the frontier object exists
  in Lean for C's objective; M4 (generic-cost wrapper) carries it to an arbitrary team loss.
- Latency caveat (best one-swap by brute force is k(m−k) evaluations; a budget-conditioned net is
  one forward pass): correct and must be measured.
- **The N-axis (A's role) is the right addition, and it is less of a graft than the memo thinks.**
  The loss object is ALREADY shared in Lean: `LeanPaperAModelBridgeV1` imports
  `LeanProductMixedDifferenceV4` and proves `selectedRadius_eq_compressionLoss`, i.e. A's
  compression decision uses the same product-reference compression loss as D6 and the same support
  radius as Structural/Support. A's decision is "which components to retain" — a selection. A's
  surrogate starves exactly the cells that the frozen extrema ignore (`starvation_at_optimum`), and
  in the D6 picture those are the interaction terms (mixed differences) that single-component
  scores do not see. So V(N, R) — N paid interaction measurements before the reveal, R repairs
  after — is a statement about ONE object:
  proxy (first-order) acquisition ⇒ interaction terms starved ⇒ the right repair is not
  identifiable even when R suffices for an oracle. The A7 learner is generic in the answer set and
  its alternatives, so the k-set answers of a budget can be instantiated; A6/A7 give the
  log(1/δ) vs log²(1/δ) separation as the template for "repaired acquisition vs proxy acquisition".
- Revised central theorem target (merging §12 and the memo): on a finite product-reference
  compression family, (i) commitment price of the score ranking ≤ min(k,m−k)·δ□ and = 0 when all
  score gaps ≥ 2δ□ (D6, corollaries); (ii) a revision frontier for arbitrary retained sets (new);
  (iii) a family where R = 1 suffices for the oracle but every proxy-acquisition learner needs
  Ω(log²(1/δ)) (or cannot identify the repair at fixed N), while repaired acquisition needs
  O(log(1/δ)) (A6/A7 pattern, new instantiation).

---

# Second pass (after the user's "đọc lại từ đầu tất cả"), 2026-09-27 afternoon

Re-read: this file from §0, all eleven manuscript digests (title, abstract, every displayed
statement, limitations, open problems, conclusion), ROADMAP.md, OPEN_MATH_20260924.md,
MATH_AND_NOVELTY_AUDIT_20260925.md, the 74 artifact JSONs and their provenance notes, the C
recourse producer, the MARL model code, and the Lean source wherever a manuscript and this file
disagreed. Nothing in manuscripts, Lean or scripts was changed.

## 15. Corrections to my own first pass

1. **§3 and §4 overstate the Query chain. It is NOT complete end to end in Lean.** Every
   analytic module takes the join it needs as a hypothesis, and no module anywhere composes
   them (`grep` finds no user of `hellinger_upper_const`, `hellinger_ratio_tendsto`,
   `hellinger_lower_from_interval` or `mixture_coeff_ne_zero` outside their own files).
   Each module says so in its own "WHAT THIS DOES NOT ESTABLISH" section:
   - `LeanQueryTaylorRemainderV1.hellinger_upper_const`: the envelope `|p_A − p_B| ≤ h^r·G` is
     the hypothesis `hbound`. The module names the finite-sum bookkeeping as its remaining gap.
     `iteratedDeriv_fun_sum` (MixtureDerivativeV1) now exists, but nothing applies it here.
   - `LeanQueryAnalyticLimitV1.hellinger_ratio_tendsto`: the pointwise limit (`hptw`) and the
     domination (`hdom`) are hypotheses. It is a dominated-convergence wrapper.
   - `LeanQueryHellingerIntervalV1.hellinger_lower_from_interval`: the family of bounds
     `hDbound` is a hypothesis.
   - `LeanQueryRateAssemblyV1`: `L ≤ 2H²` is the hypothesis `hLup`. The constants c± are
     measured in `scripts/P15_query_hellinger_order.py`.
   - `LeanQueryRegretChainV1`: the error bracket and both reduction steps are hypotheses.

   So the correct statement is: **every component is proved, but no assembly exists at the
   paper's mixture.**
2. **Consequence for B1** (TASKS_20260927.md). B1 is not "instantiate the chain". It must build
   the joins itself, at a fixed η, on `famLaw`:
   - (a) the order-r Taylor envelope for a finite Gaussian mixture, composing
     `iteratedDeriv_fun_sum`, `bound_of_vanishing_derivs` and `component_deriv_envelope`;
   - (b) the pointwise limit of the normalised integrand;
   - (c) an interval `E` on which Δ_r keeps its sign, giving `hDbound`;
   - (d) the level condition of `levelSum_ne_zero`: the top level must be strictly largest
     and carry a nonzero coefficient (`htop`, `hc`).

   This is the bulk of the work. A reusable "finite Gaussian mixture ⇒ H² ≍ h^{2r}" theorem
   would close the Query paper's own gap and B's crossover at once.
3. **§8 overstates Unified.** `LeanUnifiedQueryOrderV1` proves only the VANISHING half:
   `moment_vanishes_below_s`. Its `top_query_is_informative_at_first_order` is the trivial
   d = n case. Attainment of s!/s^s for general d is not formalised, and the module says so.
   The unified manuscript (Limitation 2) is correct. For linear probes (d = 1), attainment is
   B's `cube_sum`/tail-moment result.
4. **§12 item 2** was already corrected in the first pass (`hTop`). It stands.

## 16. Manuscripts against Lean: staleness and inconsistencies

- **Age.**
  - The seven older manuscripts and unified were last edited on 2026-09-19: structural,
    functional, support, query, adaptive, d6, master, plus the combined `d6_functional.tex` and
    `support_query.tex`. That predates the frozen gate (2026-09-23) by four days.
  - All their PDFs date from 09-19.
  - `paper_b.pdf` (09-26 00:58) is older than `paper_b.tex` (09-26 20:53), and `paper_c.pdf`
    (15:43) is older than `paper_c.tex` (18:14). The PDFs do not show the current text.
- **Scope counts.**
  - Every older paper prints "762 files, 7,199 statements, 111 accepted modules, 857 audited
    declarations". master prints **875**, which disagrees with the other papers.
  - Current tree: 754 files, 7,704 statements.
  - The "acceptance receipts" predate the from-scratch gate (§9). None of the counts is
    reproducible from a current gate report.
- **Query overclaims its own chain.**
  - The abstract and the Conclusion (`query.tex:1392`) say the chain is "closed end to end".
  - `query.tex:593–595` says the envelope "gives H² ≤ (J/2)h^{2r}".
  - But `query.tex:817–823` itself admits that the limit theorem's hypotheses are not
    established for the paper's laws. The Lean (§15.1) agrees with 817–823.
  - This is a manuscript overclaim (missing guarantee), not a Lean bug.
- **Unresolved editorial placeholders** (`\TODOPAR`/`\NOTEPAR`):

  | Manuscript | TODOPAR / NOTEPAR |
  |---|---|
  | master | 2/4 |
  | functional | 3/2 |
  | support | 2/1 |
  | query | 3/2 |
  | structural | 7/0 |
  | adaptive | 1/6 |
  | d6 | 2/2 |
  | unified | 3/4 |
  | d6_functional | 6 TODOPAR |
  | support_query | 6 TODOPAR |
  | paper_b_supplement | 2/20 |
  | paper_a, paper_b, paper_c | 0 |

  Examples:
  - functional's TODOPAR: the title was narrowed because the separability step is unproved.
  - support's TODOPAR: the decoder is not uniquely optimal; K-independence is an identity of
    the symmetric model.
- **Template residue** "a further $0$ audited declarations" occurs in adaptive:432, d6:571,669,
  functional:332, query:507, structural:480,796, support:362,504, and the combined files.
- **Paper B.**
  - `thm:attain` still says the decision-probe second moment is "computed by hand \CERT".
    `LeanPaperBDecisionMomentV1` is gated (smokeB2_20260926).
  - Limitation 5 ("the Taylor remainder behind [the parity critical constants] is not
    formalized") will become partly stale once `LeanPaperBParityCriticalV1` is finished and
    gated. It has `chi_limit`/`kl_limit` but not `parity_critical_game`.
  - Supplement 398–399, η ≍ h: wrong (§13).
- **Paper C.** Limitation 5 (odd one exchange numerical only) matches the Lean: `BudgetExchangeOddV1`
  is incomplete.
- **Paper A.** Limitations match the ROADMAP open items. These are: policy-level budget
  constant on the family; the implemented learner's rate; deployable re-solving; closed forms
  in M.
- **OPEN_MATH_20260924.md, last block.** "The ratio breakpoints are not identified exactly" is
  stale. Row C4 of the same file records the exact breakpoints (5−2√2, 7−2√6, …), closed
  2026-09-26.

## 17. Artifact provenance (all 74 JSONs in research/unified_20260919)

- For each artifact, I compared every 64-hex hash it records against the sha256 of every
  current script.
- **Matches.** 58 live artifacts match their current producer. Four older artifacts carry no
  hash and are superseded by `*_corrected_v2`: obstruction_order, oracle_gap, query_order,
  structural_frontier.
- **Mismatches, each documented:**
  - `paperA7_learner`, `paperA_deployable`, `paperA_mechanism`, `paperB_decoder`: launch
    source ≠ current source, recorded in their `*.PROVENANCE_NOTE.md`. The figure JSONs record
    both the launch and the current producer hash.
  - `paperC_perturbation.json`: recorded producer 89ccb1d4… equals `git show 51993ef`. The
    current source (565e055) only adds SKIPS logging, and the script itself states that the
    launch had no skips (row counts equal the grid). Benign, but it has no PROVENANCE_NOTE of
    its own; the explanation lives in the script and in `paperC_robustness.AUDIT_NOTE.md`.
  - Smoke files `paperB_crossover_smoke`, `paperC_typed_frontier_smoke`,
    `paperC_robustness_smoke`: producers were edited after the smoke run. The manuscripts do
    not use them.
- **The registry `_provenance.json` is stale.** It is dated 2026-09-22 and says
  "all_live_current": true. Many artifacts listed above postdate it. Regenerating it would
  overwrite an artifact; per the no-overwrite rule, a new dated registry should be written
  instead.

## 18. Result-to-algorithm audit: `paperC_budget_recourse.json` (the recourse evidence)

- **Model.**
  - The LP is the typed count flow of U, plus a per-budget transport of radius R.
  - The band is applied to the base law at every budget and to the final law. The regret is
    that of the final law, maximised over interior k.
  - This matches `recourseSet`/`PlanFeasible` in `LeanPaperCBudgetAwareV1`: the base ranking
    law is band-feasible, each budget has its own edit plan, the final law is band-feasible,
    and the cost is the sup over k.
  - The docstring's "lift to item exchanges NOT formalized" is stale in the favourable
    direction: `recourse_eq_count` (CountRecourseV1) proves the count model exact.
- **Solver and self-checks.**
  - A HiGHS failure raises instead of being skipped.
  - The self-checks can fail: they compare against closed Lean formulas for four items and
    g_m, check the chain B ≤ V^(R+1) ≤ V^(R) ≤ U, and check V^(⌊m/2⌋) = B.
  - Tolerance is 1e-7 absolute, against values of order 1e-2. Evidence class NUMERICAL.
  - No algorithmic error found.
- **Finding (important for the MARL direction).** In EVERY cell of the artifact, the least R
  with V^(R) = B is 0 or 1:
  - g_m for m = 4..10 at 121 bands;
  - counts (1,1,2,2) and (2,2,2,2) at ratios 1.5, 2, 2.6, 3, 5.

  The largest V^(1) − B is 3.3e-16, while U − B reaches 0.083. On C's objective, the
  "revision frontier" is degenerate: one exchange recovers the whole price, or no exchange is
  needed. The XOR three-message game (M3) has the same property. A MARL T1 whose frontier
  rests on these instances would have nothing to show between R = 0 and R = 1.

## 19. MARL code assets: information access

- **`models/core_behavior.py:474–495` (`step_population`).**
  - For every ego and every candidate neighbour j, it reads `obs_j` and `action_j` at every
    step, to update the shadow state s_ij. Only z_ij is restricted to active cores.
  - In a decentralised deployment that read IS communication. The existing budget therefore
    saves compute, not bandwidth.
  - A budget-adaptive communication experiment must enforce the budget at the information
    access (what agent i may read from j). Otherwise every "limited message" policy silently
    sees all neighbours.
- **`models/policy_value.py` (`PolicyValueNet.forward`).** It returns `(logits, value)`: an
  actor and a scalar state value. There is no critic over message or neighbour SETS, so
  neither the interaction strength δ□ (mixed differences) nor the score margin of §12 can be
  measured. The falsifiable prediction of §12 needs a set-valued team critic Q(s, S). That
  could be a learned critic evaluated on subsets, or an oracle rollout estimate on small
  neighbourhoods, labelled as such.
- **kprefix tier-A benchmark (m = 5).** It is development-only, and policy returns were
  deferred (§10). No learned-MARL result exists to audit. The new_chains_v2 MARL runners are
  plumbing smoke only.

## 20. Literature added in this pass

| Work | What it does | Bearing on the MARL paper |
|---|---|---|
| SLIM, arXiv 2605.21085 (read in full) | normalised per-agent budget β = sparsity × rounds × dimension; **trains a separate model per β** (4 seeds × 7 β); nested only by dimension truncation; no theory | a single budget-agnostic policy with revision, with theory, is not done there |
| Where2comm, NeurIPS 2022 | one perception model for varying bandwidth by truncating a confidence map | the R = 0 universal-ranking baseline, in perception rather than control |
| Matryoshka representations (NeurIPS 2022); nested dropout (Rippel et al. 2014); FlexRank, Nested Subspace Networks | nested prefixes for all budgets, empirical | no theory of the PRICE of nesting found (targeted search); a D6/Structural/C theory of when nesting is free and what it costs fills a visible gap |
| CoSLight, arXiv 2405.17152 | learns a second policy that selects collaborators for traffic signal control, including non-neighbours | closest traffic baseline for "which neighbours to hear"; no budget-adaptivity claim in the abstract |
| Bounding K for robust K-adaptability, arXiv 2409.12630 | bounds the number of second-stage policies needed (linear in dimension for objective uncertainty; exponential for constraint uncertainty; NP-hard to minimise on finite sets) | the menu side (Structural χ) has a robust-optimisation analogue; a menu-versus-revision theorem for unknown cardinality was not found |
| Recoverable robust optimisation with commitment (Math. Prog. 2026, arXiv 2306.08546); Chassein–Goerigk–Kasperski–Zieliński EJOR 2018 | commit, then bounded recovery | the recourse side is classical; novelty must come from the interaction-parameterised frontier |

## 21. Revised verdict (supersedes §12's "central theorem" paragraph where they differ)

The direction remains the right one. The re-reading changes three things.

1. **The revision frontier must be non-degenerate, and that is now the decisive open question.**
   - All existing instances, in C and in the XOR game, have R* ≤ 1 (§18).
   - The theorem that would make "limited revision" a real axis is either:
     - (i) the D6 arbitrary-set frontier (M2), ℓ_S − ℓ_T ≤ |S\T|·δ□ + deficit, together with a
       family where the exchange distance d_k grows and the frontier (d_k − R)_+·δ□ is
       attained; or
     - (ii) a Structural family (staircase, χ = r unbounded) in which the least R reaching B
       grows with r.
   - Which of the two exists is unknown. Structural's `BudgetRecourseV1` (deletions forced
     between budget-optimal selections) is the natural starting point for (ii).
   - The smallest useful computation, NOT run in this research-only turn: the exact LP for
     V^(R), with the C producer's model, on the Structural staircase family and on D6 witnesses
     with m ≤ 8. The question it answers: is min{R : V^(R) = B} > 1 anywhere?
2. **Broader framing, higher novelty.** Frame the paper as the price of nesting for
   universal (truncation) policies — Matryoshka, Where2comm and CoLight-style attention all
   use one:
   - zero price when all score gaps are ≥ 2δ□ (D6 `margin_two_sufficient`, all-cut
     corollary);
   - price ≤ min(k, m−k)·δ□, sharp at m = 6 (D6);
   - one ranking is always within 2/3 (Structural);
   - menus of χ ≤ ⌊2/ε⌋+1 rankings suffice (Structural);
   - what revision buys (the new theorem).

   MARL traffic control is the application, with a moving-traffic staleness rule from
   Functional LIFE. No theory of this price was found for learned nested representations or
   messages.
3. **The experiment needs two things the code does not have.**
   - The budget must be enforced at information access (§19).
   - A set-valued team critic is needed so that δ□ and the margin can be measured. Without it,
     the theory's prediction ("revision helps exactly where δ□/margin is large") cannot be
     tested.

Before any MARL manuscript text:
- the old-paper gate (smokeOLD7, running) must pass for the D6, Structural and Functional
  modules the paper would cite;
- M1 (D6 corollaries) and M4 (generic-cost wrapper) are short;
- M2 or the frontier-family question of item 1 is the make-or-break theorem;
- the B1 scope is as in §15.2.

## 22. Files named in the MARL synthesis memo, read in full this pass

- **`models/peripheral_memory.py` (v2).** Its header records the ORIGINAL CIG-AMF MARL null
  result. Without the multi-memory module: Core F1 0.251/0.259 and throughput 241.8. With it:
  0.244/0.262 and 74.7. So the main module gave no measurable benefit at 3.2× the compute.
  Also, `build_inputs` reads neighbours' `last_actions` and `compact_relation_features` for
  every neighbour. This is a second free information channel, like `core_behavior.py:474–495`.
- **`scripts/run_paper_b_allocation.py`.** Its old "Paper-B" label predates today's paper B.
  - It compares matched-budget selector-isolation panels (C-, AbsD-, Random-, Correlation-,
    Attention-, WeakPrior- and Oracle-C-Core, plus Full-Explicit) on `RE.make_main_env`
    (`task_mode="behavioral_drift"`, 24 agents).
  - Its metric is decision fidelity to the Full-Explicit argmax on a held-out state bank.
  - No output artifact of this runner exists in the tree; only .pyc files are present.
  - Reusable ideas: matched budget, a full-information decision reference, and an oracle
    capacity selector.
- **`research/imported_codex_tree_20260907/KE_HOACH_6_PAPER_20260907.md`.** Items relevant now:
  - Query §7, "Dừng: chữa all-zero CityFlow bằng metric đẹp". CityFlow produced degenerate
    all-zero targets before. The 1-hop oracle diagnostic of 2026-09-27 (82% δ = 0) must be read
    in that light and reported as is.
  - Structural §5: a K-menu benchmark (Best-Chain + COVER-RANK against Top-C, one optimised
    ranking, K rankings and per-budget optima) was planned and never run.
  - D6 §6: the m = 2 supremum is 1 (by hand). The upper-bound corollary is exactly what
    LeanMarlRevisionFrontierV1 now proves generally.

## 23. Update, 27/09 afternoon–evening: new Lean results, gates, and the MARL evidence chain

Everything in this section is compiled with standard axioms and 0 sorry unless stated otherwise.
**Nothing here is gated yet.** Gate `smokeMARL17_20260927` (17 roots, 146-module closure, J=1)
was launched at 19:01:16. Ledgers (ROADMAP / OPEN_MATH / THEOREM_MAP) are not edited, per the user
rule.

### 23.1 A/B/C results that close listed limitations once gated

- **B1, the crossover rate.** `LeanPaperBCrossoverRateV1`:
  - `crossover_upper`: χ² ≤ Kx·(η²h⁴ + h⁶) uniformly;
  - `crossover_eta_of_order_h`: η = ch gives O(h⁶);
  - `crossover_fixed_eta`: h⁴ limit 32η²/(3+η)⁴·c₂;
  - `crossover_zero_eta`: h⁶ limit 2c₃;
  - `crossover_constants_pos`.

  **Consequence.** paper_b_supplement.tex lines 398–399 in the 12:00 version claimed that η ≍ h
  changes the exponent. That claim is refuted. Another session EDITED the supplement at 14:02
  (lines 400–402 now say order h⁶ along η = ch). This is a manuscript edit that precedes gating;
  keeping it is the user's decision.
- **B2.** `LeanPaperBParityCriticalGameV1.parity_critical_game` (+ `_satisfiable`) closes paper_b
  Limitation 5, the parity critical constants. It supersedes §7/§15 lines 196 and 603, which said
  the declaration was absent. `LeanPaperBParityCriticalV1` had 9 compile errors; it is fixed, and
  the pre-fix copy is in legacy/.
- **C1.** `LeanPaperCBudgetExchangeOddV2.recourse_one_odd_all` (V^(1) = B for every odd m ≥ 3 and
  every η) closes paper_c Limitation 5, the odd one-exchange case.

### 23.2 New MARL Lean modules

| module | content | theorems |
|---|---|---|
| `LeanMarlEstimatedRevisionV1` (T1) | deployable regret 2(δ+u)(d−R)₊ + 2ε + ν + ζ; certificate with δ_U; the coefficients 2u and 2ε are sharp | 12 |
| `LeanMarlRepairCalibrationV1` (T2) | needle class on one Gaussian query channel (details below) | 18 |
| `LeanMarlTabulationV1` | per-budget tabulation has no geometric term and dominates revision | 5 |
| `LeanMarlProfileSearchV1` | finite-search bound on the heterogeneous profile space; private decomposition | 4 |
| `LeanMarlRevisionAuditBridgeV1` | written by another session, uncompiled until the gate | — |

T2 in detail:
- per-repair lower bound;
- calibration cost ≥ |Amb|·((1−α)log(1/α) − log 2)/(β²/2);
- constructive upper bound |Amb|·⌈8 log(|Amb|/α)/β²⌉;
- margin empties Amb;
- |Amb| ≥ C(k,R)C(m−k,R) for the R-dependent problem. This is NOT a claim that more rights need
  more data on a fixed problem.
- zero allocation is impossible;
- geometric floor.

### 23.3 Gates

**smokeOLD7 (the seven older papers + unified)** finished at 13:47.
- 251/251 built, 0 errors, 0 sorryAx.
- 1,455 audited theorems, closure {Classical.choice, Quot.sound, propext}.
- SMOKE FAIL comes only from two classification flags:
  - `imports_closed = 0`: the Aesop import in `LeanD6AllocationFiniteBridgeV1`;
  - `native_decide = 10`: a source-level count in the dependency
    `LeanStructuralScalarChi5WitnessV1`, which is in no audited closure. The kernel replacement
    `LeanStructuralScalarChi5KernelV1` exists.
- All 120 cited modules are clean in every paper.
- Fixing the Aesop classification in `verify_all.sh` is coordinator-owned and awaits the user.

### 23.4 MARL evidence chain

All of this is oracle or diagnostic, on a frozen MP2 actor with held-phase H = 3. It is not
learned MARL. The files are in `research/marl_budget/`.

| result | file | reading |
|---|---|---|
| Latency premise of PROTOCOL_v1 refuted | LATENCY_PREMISE_CHECK_20260927.md + LeanMarlTabulationV1 | A per-budget table is looked up in 0.1 µs, against 0.3–0.5 µs for a prefix and 7–59 µs for repair. The priority saves about 40 µs before the grant. |
| Global-broadcast oracle screen | same file | Loss comes from the score, not from nesting: best nested chain 0.33 against heuristic prefix 23.1. |
| Learned selectors under PROTOCOL_v1 | CHEAP_CHECKS_V2_RESULTS_20260927.md (+ v3 trainer) | No held-out improvement over the heuristic; the unseen-budget check was not robust across v2/v3. |
| Heterogeneous receivers, exact, preregistered | HETERO_EXACT_RESULTS_20260927.md, PROTOCOL_HETERO_v0.md | R=1 recovers 88% of the private gap, 16/16 episodes; private beats the EXACT known-budget shared order in 106/256 cases; +16 B per step. |
| Step 3 pilot, legal learned repair | HETERO_PILOT_RESULTS_20260927.md | +0.9 to +1.4 against oracle +25 (true-scored uncapped search attains exact R1). Direct search with the same critic is indistinguishable. |
| Legal receiver-history mirror + learner diagnostic v1/v2 | HETERO_DIAGNOSTIC_{,V2_}RESULTS_20260927.md | After anchoring, prefix-favouring ties and inner-selected no-edit thresholds, no legal predictor improves repeatably at +28 B (best −0.15 … +0.78). |
| Privileged ablation | same | Joint actions ALONE recover about half the oracle headroom (+7.1 to +8.0), mostly at headway 8; current summaries alone do not help. |

**Decision per the independent audits (MARL_SCOPE_AFTER_CHEAP_TESTS,
MARL_HETERO_DIAGNOSTIC_INDEPENDENT_AUDIT).** Stop the learned-traffic expansion for this
submission cycle. No empirically successful learned MARL method can be claimed.

What remains supportable:
- the mathematics (T1, T2, tabulation, profile search, and the revision / nesting / XOR results);
- the exact oracle mechanism;
- the diagnostic negative results. Actor-response prediction is ONE candidate bottleneck, not a
  proven one.

### 23.5 Corrections to claims made in this session (all fixed in the result files)

1. "More rights need combinatorially more data" compared R-dependent problems. It is now restated
   as a worst case over an R-dependent class.
2. "Information ceiling" is only privileged current summaries.
3. "Data-starved" is an unresolved generalisation gap.
4. "Charged bids" was an offline feature ablation.
5. "ν ≈ 0, ε large" holds only for true-scored uncapped search. It says nothing about the learned
   search's ν or ζ, and MSE is not ε.
6. "Action prediction is THE barrier" became "one candidate bottleneck".
7. The v1 diagnostic had a tie/anchoring bug and did not select a threshold. Fixed in v2.
8. The heterogeneous check v2 optimised the shared order after the budget draw and had no R bound.
   It was replaced by the preregistered exact oracle.

### 23.6 Big-work items done after §23.5 (27/09, 19:00–19:40)

**E1, controlled calibration** (`research/marl_budget/E1_CONTROLLED_RESULTS_20260927.md`).
- On the exact T2 model, the α-cost measured for targeted block tests lies between the proved
  lower and upper bounds for |Amb| = 9 … 125.
- The symmetric all-k-set design pays about (C(m,k) − 1)/|Amb| times more.
- Proxy-only never succeeds.
- On an executable Bayes-decoder task with a hidden interacting pair:
  - R = 2 has floor 0 but is worse than R = 1 until about 25k paired rollouts, and better at 51k.
    This is the two-cost law.
  - Singleton-importance acquisition never improves on the prefix.
- A first E1 run with an anti-conservative plug-in-z rule is superseded and kept. Its figures are in
  legacy/.

**Four main figures:** `research/marl_budget/figures_20260927/` (fig1 to fig4), built only from saved
artifacts, each with its evidence class in the title.

**New Lean modules**, compiling as this is written. They are not in gate `smokeMARL17`, so they need
the next gate.
- `LeanMarlBlockFrontierV1`: T1 for heterogeneous receivers. `block_frontier` gives
  2η·Σ_b(|P_b \ T_b| − R)₊ on per-block (partition-matroid) profiles with a coupled team value;
  also `block_zero_price` and satisfiability.
- `LeanMarlStarvationV1`: `allocation_starvation` (cost ≥ D/(ρβ²/2)) and `symmetric_design_cost`
  (≥ (C(m,k) − 1)·D/(β²/2)).

**Still open (math):**
- T2 log|Amb| gap;
- shared-pair lower bound (E1b is its empirical case);
- all-budget repair table;
- probabilistic δ_U certificate (the deterministic +4ε transfer is in `LeanMarlRevisionAuditBridgeV1`);
- actor realization of the edge-local hypothesis.

**Blocked:** E2 and E3 (learned actor, SchedNet, closed loop), by the audit stop rule.

### 23.7 T2 math debts closed after §23.6 (27/09, 19:40–20:30)

None of these modules is in gate `smokeMARL17`; all need the next gate. Each was compiled standalone
against the scratch olean of `LeanMarlRepairCalibrationV1`. Each reports only
[propext, Classical.choice, Quot.sound] and has 0 sorry. Source sha256 prefixes: CalibrationGap
c2484946…, PairCalibration 6206d699…, BlockFrontier 3fdde642…, Starvation 739ef1fe…

**`LeanMarlCalibrationGapV1` (8 theorems): the log|Amb| gap, located.**
- `own_world_lower` is the reverse change of measure (needle world → null world) on the event
  {out = T}. `null_mass_le`: the null probabilities of the disjoint events {out = T}, T ∈ Amb, sum
  to ≤ α. `log_sum_ge` is Jensen via log x ≤ x − 1.
- `own_world_sum`, for ANY adaptive protocol:
  |Amb|·((1−α)log(|Amb|/2α) − log 2) ≤ (Σ_T E_T[N_T])·β²/2.
  The log|Amb| factor is real, but each needle world pays it on its own needle.
- `sched_calibration_lower`, for a FIXED schedule: counts do not depend on the world, so the same
  bound holds for the cost in every world.
- `sched_upper` restates `calibration_upper` with its schedule explicit.
- Within fixed schedules, cost is Θ(|Amb| log(|Amb|/α)/β²). The ratio of the two bounds tends to
  4/(1−α).
- `sched_satisfiable`: |Amb| ≥ 4, the bound is > 0, and the explicit schedule meets every hypothesis.
- **Correction made in the source before recording.** A draft docstring said the constant ratio is
  "about 16"; the correct value is 4/(1−α).
- **Not proved:** an adaptive upper bound.

**Two-stage numerical diagnostic** (`scripts/MARL_E1a_two_stage.py`, sha 5da21441…).
- Result: `research/marl_budget/e1a_two_stage_20260927_194136/results.json`, seed 0, default grid,
  COMPLETE.
- Model: the exact needle model. Error probabilities of the fixed and screen-then-confirm designs
  come from exact independent-Gaussian formulas, and each design is optimised on a grid.
- Self-checks (the script refuses to write on failure): all three compiled bounds hold for the
  optimised designs. A Monte-Carlo run (200k trials, M = 64) reproduces the analytic errors: null
  0.00535 vs 0.0054, needle 0.0499 vs 0.0496.
- The smoke run caught a sign error in the needle-fire probability before the full run. The failing
  version wrote nothing.
- Findings:
  - the two-stage worst-world expected cost is below `sched_calibration_lower` for |Amb| ≥ 256
    (α = 0.05) and |Amb| ≥ 1024 (α = 0.01), falling to 0.6× that bound at |Amb| = 65536;
  - it stays within 3.6× of `calibration_lower` for every tested |Amb| from 4 to 65536;
  - the ratio creeps up slowly, from 3.0 to 3.35 at α = 0.05, so no constant-factor claim is made.
- Evidence class: NUMERICAL. Adaptivity removing the factor is not a theorem.

**`LeanMarlPairCalibrationV1` (10 theorems): the shared-pair class, which is the class of E1b.**
- Pair world: excess β on every broadcast set ⊇ E, |E| = 2.
- AmbP: E ⊄ P; every reachable S ⊇ E has deficit > ε; some has deficit < β − ε.
- `pair_one_lower`, `pair_calibration_lower`, for any adaptive protocol:
  |AmbP|·D ≤ (Σ_q E_0[N_q]·cov q)·β²/2, where cov q counts the ambiguous pairs inside query q.
- `pairs_cover_le`: a set contains at most |S \ P|·|S| pairs not inside P.
- `pair_legal_lower`: if only legal repairs are rolled out (null-world expected count 0 off
  F_R(P)), then |AmbP|·D ≤ R·k·E_0[cost]·β²/2. One legal rollout informs up to R·k pairs, where the
  needle law allows one repair per query.
- `pair_upper` is a legal fixed schedule: block tests on every reachable non-prefix set, decoded to
  the fired set of largest first-order value.
  - It is correct at the null world and at every ambiguous pair. Its cost is
    |F_R\{P}|·⌈8 log(|F_R\{P}|/α)/β²⌉.
  - It rests on `rnofire_gen` (a missed firing in any world with excess β) and on
    `err_pattern_world`, a union bound that works for any decoder right on the pattern event.
- `pair_satisfiable`: m = 4, |P| = 2, R = 1. |AmbP| ≥ 4, the bound is > 0, and the protocol
  meets every hypothesis, legality included.
- **Not established:**
  - tightness: no design reaching |AmbP|/(Rk) is built;
  - worlds with several pairs or higher-order interactions;
  - queries outside F_R(P).

**Still open (math):**
- an adaptive T2 upper bound (needs the history law of an adaptive Policy);
- a tight design for the pair class;
- the all-budget repair table;
- a probabilistic δ_U certificate;
- actor realization of the edge-local hypothesis (candidate: the E1b Bayes decoder);
- T1 drift beyond the AuditBridge.

**Gate `smokeMARL17`:** 31/146 modules exited, all 0, at the time of writing.

### 23.8 B1 learning curve (27/09, 20:14–21:35). The user lifted the stop rule for this test only.

- Protocol preregistered: `research/marl_budget/PROTOCOL_B1_LEARNING_CURVE_20260927.md`, sha e84ca65f…,
  identical in the collector manifests and the training report.
- Results: `research/marl_budget/B1_LEARNING_CURVE_RESULTS_20260927.md`; run
  `b1_lc_20260927_201443/`. 960 fresh oracle-labelled records: seeds 301–364, 401–408 and 501–508,
  never used before.
- **FAIL by the preregistered rule.**
  - The primary legal learner `mlp_history` at N = 64 gains +0.19 [−0.35, +0.75], 1.4% of oracle R1
    (+13.33). Two of three initialisation seeds are negative.
  - The privileged joint-action reference gains +8.3 to +8.8 at every N (62–66% of oracle), CI far
    above 0.
  - Legal learners are flat in N, at 1–7% of the oracle.
- **Conclusion:** the pilot failure is an information bottleneck (the actors' response), not a data
  scale problem. No legal learned selector is claimed.
- The next step named by the protocol is B2 (a paid fresh-bid protocol). It needs a new
  authorisation.
- Self-checks passed:
  - replay reproduction and mirror = caches;
  - seed-disjoint splits;
  - prefix delta 0;
  - oracle gain ≥ 0;
  - sources unchanged.

### 23.9 Gate `smokeMARL17_20260927`: SMOKE PASS (finished 21:54)

- **Result:** 146 modules (17 listed, 129 dependencies), failed 0, not_built 0. 1298 theorems
  audited, sorry 0, native_decide 0, imports_closed = 1. The axiom closure is
  {propext, Classical.choice, Quot.sound}. DRIFT.txt is empty. The report is in
  `work/gate_runs/smokeMARL17_20260927/report/`.
- **Covered, now smoke-gated:**
  - the 9 MARL modules (RevisionFrontier, NestingDegreeGeneral, SubsetFrontier, ProxyBlindness,
    MenuRevision, XorGame, GenericRecourse);
  - T1 (EstimatedRevision), T2 (RepairCalibration), Tabulation, ProfileSearch, RevisionAuditBridge;
  - C odd V1/V2 (C1), B parity critical and game (B2), B crossover (B1).
- **Caveat.** `LeanPaperCBudgetExchangeOddV1` and `LeanPaperBParityCriticalV1` contain no
  `#print axioms` (prints = 0), so their own theorems are not axiom-audited in this gate.
  - Both pass the source scan (sorry_src = 0, native_src = 0).
  - Their importers (OddV2, ParityCriticalGame) print axioms for theorems that depend on them.
  - Adding the prints is a one-line fix per module for the next gate.
- **NOT in this gate; they need the next gate:** BlockFrontier, Starvation, CalibrationGap,
  PairCalibration. Each compiled standalone with standard axioms (§23.6–§23.7).
- **Unlike smokeOLD7, this is SMOKE PASS.** The Aesop import-flag artefact did not arise for this
  module set. The coordinator decision on `verify_all.sh` is still open for the old-paper set.

### 23.10 Corrections, gate4, and the CityFlow mitigation work (27/09, 22:10–22:45)

- **§23.8 wording is corrected** (MARL_B1_INDEPENDENT_VERDICT). Replace "not a data-scale failure;
  information bottleneck confirmed" with: "growing the pool 8→64 did not close the gap for these
  learner/representation/selection choices; counterfactual joint actions substantially improved
  prediction and selection". This supports an actor-response hypothesis without identifying it.
  - Action-change rates in the chat report were per group, not per edit.
  - The corrections are recorded in `B1_LEARNING_CURVE_RESULTS_20260927.md`.
- **Gate `smokeMARL4_20260927`: SMOKE PASS.** 39 modules, 361 audited theorems, 0 failed, 0 sorry,
  standard axioms, finished 22:10. BlockFrontier, Starvation, CalibrationGap and PairCalibration
  are now smoke-gated.
- **Response diagnostics on B1 data** (`MARL_hetero_response_replay.py`, run dirs `response_*`).
  - Legal frozen-MP2 prediction, built from scheduler-known data:
    - absolute action accuracy 0.103, against a chance level of 0.125;
    - per-receiver change prediction: precision 0.29, recall 0.09, base rate 0.21;
    - the legal score gap does not predict change (0.20–0.23 in every quintile).
  - Receiver-LOCAL quantities computed before transmission:
    - the preferred action matches the true prefix action 0.674 of the time;
    - the local score gap predicts change: 0.30 in the lowest quintile, 0.10 in the highest.
  - Debug of one snapshot: the view code is correct. The poor legal accuracy comes from queue
    changes between stale packets and the present, with near-tied MP2 phases.
- **Started:** the mitigation development screen (`mitigation_dev_*`, 10 learners × 3 seeds, on
  opened B1 data, development only); B2 infrastructure (preregistered protocol with a
  design-freeze guard, collector, frozen-model confirmation, runner); a closed-loop evaluator.

### 23.11 CityFlow mitigation screens, B2 freeze, closed-loop oracle, E1 fixes (27/09, 22:10–23:10)

- **Mitigation development screens** (`research/marl_budget/MITIGATION_DEV_RESULTS_20260927.md`,
  table `MITIGATION_DEV_TABLE_20260927.txt`). DEVELOPMENT evidence on opened B1 data.
  - Auxiliary actor-response supervision does not help reliably.
  - Positive differences with CI > 0 against the chosen no-bid control at the same total cap
    (bids charged):
    - `struct_legal` (legal, frozen MP2 on scheduler-known data) at +28;
    - `bid_prefgap` at every cap;
    - `mlp_top2` R1;
    - `mlp_top2_joint` direct at +56/+84.
  - Best: +3.19 against +1.61 at +84 direct, about 20% of the oracle.
  - The privileged reference, retrained in the same trainer, reproduces B1: +8.2 to +8.7 at +28,
    and 84% of the oracle at +84 direct. The trainer is therefore not the bottleneck.
- **B2.**
  - Protocol preregistered at 22:20. Amendment 1 (22:55) added the learned request, top-2 and
    top-2-joint bids before any freeze.
  - The mechanical freeze (`scripts/MARL_hetero_b2_freeze.py`) chose mlp_top2_joint / direct /
    +84 / ctrl_history, with a development difference of +1.58.
  - The confirmation on fresh seeds 601–616 was launched with frozen models, τ and stage A
    (`scripts/RUN_marl_b2_confirm_v2.sh`).
- **Closed-loop oracle headroom** (`MARL_hetero_closed_loop.py`, 16 development episodes):
  - Σ waiting −9.6% at +28 (13/16 better) and −10.3% at +56 (14/16);
  - +14.5 / +14.9 finished trips;
  - +5% / +10% bytes.
  - Held-phase repair value is realised in closed loop. The reference is not deployable.
- **E1 corrections done** (`E1_CONTROLLED_RESULTS_20260927.md`, "Corrections" section):
  - the E1b/Gaussian-channel separation, with the witness cited;
  - the R2-crossover wording; targeted ≡ uniform; the proxy scope; adaptive marked exploratory;
  - nominal N in E1a;
  - two-stage v2 with a literal decoder check (rows identical);
  - figures v2 (`figures_20260927_v2`).
- **New Lean:** `LeanMarlE1bRealizationV1` (e1b_marginal, e1b_scoreLocal, e1b_scoreLocal_half,
  e1b_mono, e1b_satisfiable). It compiles standalone with standard axioms and needs the next gate.
- **Still open from the E1 audit:**
  - a Gaussian shared-pair experiment that instantiates `rChan`, if the pair theorem is to be
    tested empirically;
  - the pair-tightness LP.

### 23.12 B2 PASS (held phase), B3 FAIL (closed loop) with diagnosis, E1b gate (27/09, 22:50–23:10)

- **B2 confirmation** on fresh seeds 601–616 (`B2_CONFIRMATION_RESULTS_20260927.md`): **PASS**.
  - The frozen mlp_top2_joint / direct / +84 beats ctrl_history by +1.85 [+0.95, +2.84].
  - Its gain is +3.12, about 18% of the oracle; seeds +3.90 / +2.98 / +2.48; bid_queue +0.98.
  - Provenance is clean: freeze at 22:49:52, labels at 22:51, one protocol hash throughout.
- **B3 closed loop** (`B3_CLOSED_LOOP_RESULTS_20260927.md`): **FAIL**.
  - Σ waiting against the control −0.26% [−1.20%, +0.62%]; the oracle reference gets −14.5%.
  - Diagnosis:
    - parity between the closed-loop and confirmation predictions holds to 5e-6;
    - shadow mode on the prefix trajectory would edit at 13–16 of 16 steps;
    - in closed loop the selector stops editing after its first patches.
  - This is covariate shift induced by the policy: the models were trained only on
    prefix-trajectory states.
- **Gate `smokeMARL1_E1b_20260927`: SMOKE PASS.** 4 modules, 28 audited theorems, 0 sorry,
  standard axioms. `LeanMarlE1bRealizationV1` is smoke-gated.

### 23.13 B5 FAIL (borderline), B6 robustness, η bridge, full endpoints, critical-path status (27/09, 23:15–23:40)

- **B5 (struct_legal, legal-only).** FAIL on c1: Δ +1.02 [−0.04, +2.13]; c2 and c3 pass.
  Consistent but unconfirmed.
- **B6 (descriptive).**
  - The B2 design keeps its advantage under held-out heavy and light loads (CI > 0).
  - It does not keep it under fixed, bursty or low capacity processes.
  - The privileged reference stays strong everywhere.
  - Correction: every earlier hetero panel used i.i.d. capacities; the "bursty" spec is
    overwritten.
  - `B5_B6_RESULTS_20260927.md`.
- **η bridge** (`MARL_hetero_eta_bridge.py`, `eta_bridge_20260927.json`). An exact Chebyshev LP
  over one-swaps of the TRUE values: 75.7% of 24,692 (state, receiver) pairs have η = 0; p90 is
  1.375; 63% satisfy T1's zero-price cut condition. This is empirical, not a proof.
- **Full closed-loop endpoints for B3** (`MARL_hetero_closed_loop_report.py`): censored travel
  time and throughput; the oracle-access self-check passes.
- **Live panel collector** (`MARL_hetero_panel_collect.py`): it reproduces the replay pipeline
  EXACTLY on seed 301 (labels, joint, mirror, response, both bids).
- **Structural flip model for stage A** (bid gap + MP2 coefficients × (latest − cached)). Accuracy
  0.692 against 0.686 for always-p1. Change precision 0.49 against a base rate of about 0.21;
  recall 0.08. Informative in precision only.
- **Critical-path status:** `research/papers/audits/MARL_CRITICAL_PATH_STATUS_20260927.md`.

### 23.14 Baseline panel, independent direct, stage A v2, and the independent recheck's corrections (27/09, 23:30–23:50)

Details are in `research/marl_budget/BASELINES_DIRECT_STAGEA2_RESULTS_20260927.md`. The
independent recheck (`MARL_CRITICAL_PATH_INDEPENDENT_RECHECK_20260927.md`) was verified finding by
finding against the code.

- **Correction to §23.13 (η bridge).**
  - The LP fits only one-swaps around P. Its η is a lower bound, and "63% satisfy T1's zero-price
    cut condition" certifies nothing globally.
  - Counterexample: f = 1 iff {2,3} ⊆ S.
  - Correct labels: one-swap additive residual; fitted local no-improvement 63.3%; direct local
    no-improvement 72.5%.
  - The T1 → traffic bridge is OPEN.
- **Correction (request baseline).**
  - `MARL_hetero_closed_loop_v3.py:59–70` ordered receivers by the exact gap, which is not in the
    1 B bid.
  - The new producer `MARL_hetero_closed_loop_v4.py` orders by (gapbin, id). The v3 rows are
    kept and labelled.
  - 6/32 episodes change; +0.39% → +0.53%. The conclusion is unchanged.
- **Label.** `schednet_fresh` and `where2comm_top2(_bin)` are heuristics, not learned
  SchedNet/Where2comm.
- **Closed-loop panel on fresh seeds 1101–1116 (32 episodes; descriptive).**

  | method | Σ waiting vs prefix | notes |
  |---|---|---|
  | frozen B2 design | −0.28% [−1.65, +1.18] | edits 1–3 of 26 steps |
  | ctrl | +0.18% | |
  | schednet_fresh | +4.70% [+2.09, +7.35] | worse than the prefix |
  | where2comm_bin | +0.53% | +25% bytes |
  | oracle | −14.4% | |

  The self-check passes. B3's failure replicates on a second fresh panel.
- **Independent direct selector (development).**
  - Unchanged at +84.
  - R1 is below the independently tuned direct selector by 1.1–1.6 at +56/+84/none (CI > 0).
  - The bid advantage survives: +1.28 [+0.11, +2.60].
  - **In traffic the method is a charged-bid direct selector, not limited revision.**
- **Stage A v2 (development).**
  - Select accuracy 0.7173 against always-p1 0.7093.
  - It helps R1 and +28 direct; it does not help +84 direct (−0.10 [−0.89, +0.64]).
  - It has 27 inputs, so it is not deployable in the current runners without a new inference path
    and a parity check.
- **Provenance.** `PROVENANCE_SUPPLEMENT_20260927.json` holds the wrapper and coefficient-JSON
  hashes; all mtimes precede their runs.
- **Latency** (§23.13 did not state this): compute only, measured under CPU contention; no uplink
  or network delay.
- **Fig 3 v3** (working): `figures_20260927_v3/`.

### 23.15 User decisions (27/09, ~23:55)

1. **Allow Aesop in `verify_all.sh`.**
   - The exemption already in the working copy is accepted. It was written by another session at
     14:02, after the OLD7 gate had finished.
   - It admits `Aesop` / `Aesop.*` imports only when Aesop is a pinned dependency: it must appear
     in `lake-manifest.json` and `.lake/packages/aesop/Aesop.lean` must exist. It is not a blanket
     exemption.
   - The same session replaced the ten `native_decide` steps of
     `LeanStructuralScalarChi5WitnessV1` with kernel `decide`, and edited the docs of
     `...KernelV1`. The pre-audit copies of both are in `legacy/`.
   - Neither change had been gated. The smoke gate `smokeAESOP_20260927` was launched to check
     them (roots: `LeanD6AllocationFiniteBridgeV1`, `LeanStructuralScalarChi5WitnessV1`,
     `LeanStructuralScalarChi5KernelV1`; 18 modules; J=2). The OLD7 report stays as it is.
2. **Keep the other session's `paper_b_supplement.tex` edit (14:02).** Lines 400–402 say order h⁶
   along η = ch, which matches `crossover_eta_of_order_h` (`LeanPaperBCrossoverRateV1`,
   smoke-gated in `smokeMARL17`).
3. **Commit.**
   - Excluded, not deleted:
     - every `*/scenarios/` directory (767 MB of CityFlow inputs, regenerated deterministically
       from the seeds);
     - the two directories still being written (`b4_run_20260927_230436`,
       `gate_runs/smokeAESOP_20260927`), to be committed when they finish.
   - `*.pt` stays ignored by the repository's `.gitignore`.

### 23.16 Corrections from `MARL_PUBLICATION_READINESS_AND_EXECUTION_20260927.md` §4 (verified 23:56)

- **§4.3.** The exact nesting degree is a conjecture. Lean has the lower bound ⌊(m+1)/4⌋
  (`LeanMarlNestingDegreeGeneralV1`, lines 19–34 say so). `MARL_NOVELTY_CHECK` line 29 is
  corrected.
- **§4.4.** "Nesting is forced" in PROTOCOL_HETERO_v0 is wrong.
  - `profile_cost` (`models/marl_hetero_selector.py:38–50`) allows explicit profiles.
  - The env decodes exactly |S_i| = K_i payloads of the union, so capacity is a DECODING budget,
    not a listening-time prefix.
  - R0 is the committed-order model; direct selection is a legitimate comparator.
  - The status doc (§4 step 1, drop list item 2) is corrected. The cardinality is exact
    (|S_i| = K_i, not ≤).
- **§4.5, open.** T1's BlockFrontier needs a top-score prefix of the same score vector and
  ScoreLocal on the relevant sets. The runtime order is the cached-queue order, and the R bound
  does not pay the coupled union-payload cost. These stay terms to be measured; they are not
  claimed to be zero.
- **§4.6.** B3's "covariate shift" becomes "consistent with". Held-phase target mismatch is a
  second hypothesis. `B3_CLOSED_LOOP_RESULTS` has an appended correction, and the status and
  results docs are corrected.
- **§4.7.** The independent direct selector is the same critic family plus candidate argmax. It
  is not a different subset-generating architecture.
- **§4.8.**
  - The provenance supplement is RETROSPECTIVE.
  - The latency bias under contention is not measured, so "upward-biased" is withdrawn.
  - Fig 3 compares operating points at one cap; it is not a Pareto frontier.

### 23.17 Gate, B4 verdict, target diagnostic, and the rest of the auditors' list (28/09, 00:00–00:20)

- **Gate `smokeAESOP_20260927`: SMOKE PASS** (finished 00:07).
  - Roots: `LeanD6AllocationFiniteBridgeV1`, `LeanStructuralScalarChi5WitnessV1`,
    `LeanStructuralScalarChi5KernelV1`.
  - 18 modules, 0 failed, 31 audited theorems.
  - `imports_closed=1`: the pinned Aesop is accepted.
  - `native_decide=0`, standard axioms, DRIFT empty.
  - Both classification flags of OLD7 are resolved for their modules. `...KernelV1` has no
    `#print axioms` lines; its ten facts are now audited through the Witness module's ten prints.
- **B4 preregistered test (801–816): PASS on all three criteria, and weak**
  (`research/marl_budget/B4_DAGGER_RESULTS_20260928.md`).
  - Checked:
    - manifest hashes equal the current sources;
    - the test seeds appear in no other manifest;
    - no oracle access by any deployable method;
    - the frozen-B2 prefix reproduces;
    - the endpoints were recomputed.
  - Retrained bid against retrained ctrl: −1.49% [−2.75, −0.23].
  - Against the prefix: −0.68% [−2.87, +1.37]. Against the frozen B2 design: +0.10%.
  - The retrained ctrl drifted to +0.89%.
  - Edits are now 16–21 steps per episode (oracle 19.5). The edit-rate symptom is cured, the
    benefit is not.
- **Target diagnostic** (`TARGET_DIAG_RESULTS_20260928.md`, producer
  `scripts/MARL_hetero_target_diag.py`).
  - Setup: 16 development states, 2,810 candidates; three self-checks that can fail, all PASS.
  - The held-phase argmax matches the continuation argmax in 1 of 16 states.
  - It captures 49% of the continuation headroom and is worse than the prefix in 4 of 16.
  - Mean Spearman correlation 0.41.
  - Reading: the target mismatch is real, but estimation error dominates, since the held-phase
    oracle still gives −15% in closed loop.
- **Independently tuned direct selectors in closed loop** (`cl_direct_indep_20260928_000001`,
  1101–1116):
  - no bid +0.68%, bid +0.34% against the prefix;
  - 1.5–2.3 edits per episode;
  - self-check PASS.
- **Idle latency** (`latency_b2_idle_20260928_000900`): median 14.8 ms against 16.6 ms busy, on the
  same seeds and steps. Compute only.
- **Readiness-audit items done:**
  - claim map in the status doc;
  - working draft `research/papers/_tex/paper_marl.tex` (compiles; theory cites gated modules
    only; results TBD beyond fixed MP2);
  - fig3 v4 (`figures_20260928_v4/`, producer `MARL_make_fig3_v4.py`);
  - `eta_bridge_20260927.relabelled.json` (corrected field names; the source JSON is unchanged);
  - `PROTOCOL_HETERO_v0.md` Amendment 1 (decoding budget, exact cardinality, explicit profiles,
    bid charging; descriptive);
  - `UNCOMMITTED_ARTIFACTS_MANIFEST_20260928.json` (92 checkpoints and 84 scenario trees kept
    out of git, with hashes; the partial first version is in legacy/);
  - the auditor's `MARL_PUBLICATION_AUDIT_RECALC_20260927.py`, run as a scratch copy so its output
    file is not overwritten, reproduces its numbers exactly;
  - the E1 figure captions already met P0.6.
- **Not done, with reasons:**
  - Stage A v2 closed-loop inference path (recheck finding 4): only needed before a v2 test, and
    none is planned, because v2 did not help at +84.
  - The venue template: the track is unconfirmed.
  - The E3 actor pilot is next (P2).

### 23.18 E3 learned actor, gates, and the CityFlow hang (28/09, 00:20–09:30)

- **Gates.**
  - `full9_20260928` VERIFY PASS: 301 modules, 2,382 audited theorems, standard axioms, drift 0.
    It is the first full gate since full7; MODS now holds every module the manuscripts cite.
  - `smokeOLD7b_20260928` SMOKE PASS: 251 modules, 1,465 theorems (OLD7's 1,455 plus the 10 new
    Chi5 prints), `imports_closed=1`, `native_decide=0`.
  - `smokeE1bU_20260928` SMOKE PASS: the new `LeanMarlE1bUniformV1`, a uniform shift halves the
    E1b constant without knowing the pair (readiness audit §5).
- **E3.**
  - Protocols written before results: PILOT, SCRATCH, ABLATION.
  - Every finished learned actor beats MP2: select −15% to −24%, development +12% to +23% for MP2
    (CI > 0).
  - G1 message use: scratch s3 and BC s3 pass; the BC pilot s0 FAILS, so the BC chain's selector
    results are recorded and not read.
  - Details in `research/marl_budget/E3_INTERIM_RESULTS_20260928.md`.
- **Learned SchedNet (v1).** +1.1% and +1.9% against the prefix; it does not beat the committed
  order.
- **Audit fix (my own code).** v1 sorted by float weights although only 1 byte is declared. v2
  quantises to 256 levels; the v1 rows are labelled.
- **Audit fix (my own code).** Closed-loop v2 at caps other than +84 must recompute feasibility
  with the run's cap. Fixed before any real run.
- **Hang.** CityFlow's engine barrier deadlocked (`pthread_cond_wait`, GIL held) in every E3
  process around 01:00–03:18.
  - `scripts/run_with_watchdog.py` and resume runners were added.
  - Relaunched at 09:13 alongside the 8 deadlocked PIDs. They are listed in
    `e3_hung_pids_at_relaunch.txt`; killing them needs the user.
- **Also done.**
  - F1 scene: a single swap gains +31 in continuation with held-phase 0 and no immediate action
    change.
  - F4 mechanism figure.
  - Selector v2 with a response head and closed-loop v3; the ablation runner.
  - `REPRODUCE_MARL_20260928.md`.
  - The draft updated.
  - Commit `3ae456b`.
