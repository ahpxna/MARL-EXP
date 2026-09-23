# Headline → theorem → construction → evidence

One row per headline claim of each paper, with an explicit status. A row is **headline**
only when a final Lean theorem states it on the paper's own construction or algorithm and
does not take the conclusion back as a hypothesis. A row that still takes such a hypothesis
is **conditional**, and is labelled so here even when the algebra downstream of the
hypothesis is fully proved.

Verification contract: `lean_exit=0`, zero errors, no `sorry`, no `sorryAx`, no
`native_decide`, axioms ⊆ `{propext, Classical.choice, Quot.sound}`.

A note on what a clean gate does and does not say. It certifies the Lean **statements** in
the corpus. It does not certify that a statement is the paper's headline, that its
hypotheses are satisfiable, or that the code implements the object the statement is about.
Those are the three places this table is for.

---

## Paper A — optimising a surrogate can cost the decision

**Model, fixed once.** Cells `e` of two arms, arm `A` with `2` actions and arm `B` with
`2+2r`; true world `θ_A = (−1/2, 1/2)`, `θ_B = (−1/8, 1/8, 0,…,0)`; variance `1` on the four
anchors and `M ≥ 1` on the `2r` middles; parameter class `Θ₀` the centred one; observation
`Y_e ~ N(λ_e, σ_e²)`; energy `I_w(θ,λ) = Σ_e w_e (θ_e−λ_e)²/(2σ_e²)`.

| # | Status | Headline | Final theorem (module) | Construction | Evidence | What it still takes |
|---|---|---|---|---|---|---|
| A-H1 | **headline** | The two information games separate after optimisation: `4/(4+2rM) ≤ Γ_true/Γ_fr ≤ 64/(9rM)`, `Γ_fr = 9/512` | `centred_separation`, `frozenGameC₀_eq` (`LeanPaperACentredV1`) | `thetaC` on `Θ₀`; witnesses `λ*`, `wCert` | `paperA_mechanism.json` | the two constants are not matched; the bracket is an order |
| A-H2 | **headline** | Every surrogate optimum starves the true alternatives; near-optima starve proportionally | `frozen_optimum_trueValueC₀_zero`, `near_optimal_trueValueC₀_le` (`LeanPaperACentredV1`); `frozen_optimum_trueValueStrict_zero` (`LeanPaperAStrictV1`) | same family; strict alternative set built and bounded | `paperA_mechanism.json` | — |
| A-H3 | **headline** | The repair frontier is an order: `9β/(128(4+2rM)) ≤ F(β) ≤ β/(8rM)`, i.e. `Θ(β/(rM))` | `frontier_two_sided`, `value_concave` (`LeanPaperAFrontierV1`) | the explicit mixture `w_β = (1−β)w_fr + βw_cert` | — | — |
| A-H4 | **conditional — NOT closed end to end** | The learner attains the benchmark at rate `1/((1−ε)Γ)` | `a7_chain_rate` (`LeanPaperA7ChainV1`); threshold-corrected form `a7_chain_rate_code_threshold` (`LeanPaperA7ThresholdV1`) | tracking + the closed-form statistic the code thresholds | `paperA7_learner.json` | `hgood`, `hinit`, `hEsum`, `hsup` — information accumulation and the expectation of the real process; and the join of the tail to a hitting time that may be infinite (`hitTime : ℕ∞` vs `τ : Ω → ℕ`) before termination follows |
| A-H5 | **partly closed** | A surrogate learner with forced exploration `t^{-1/2}` is quadratic in `log(1/α)` | `surrogate_omega_log_squared`, `separation_diverges` (`LeanPaperASurrogateV1`); **`hchange` now discharged**: `klChain_eq_scaled_visit`, `pair_bound_from_transcript`, `hchange_from_pairs`, `surrogate_omega_log_squared_closed` (`LeanPaperAChangeV1`), on data processing proved from scratch (`kl2_le_klChain`, `LeanPaperBDataProcV1`) | frozen oracle + `t^{-1/2}` exploration + the tracker | `paperA_swap.json` | the learner's own forced-exploration budget `Σ pairCount ≤ C + C'·ma` (which `sqrt_exploration_rate` supplies for the model's tracker), and the identification of the transcript's per-pair visit count with the tracker's middle-cell count. The stopped change of measure is no longer assumed |

**Closed this round, on A-H4's path** (each removes a specific link, none is a headline):

* the `n^{-4}` confidence step is now produced from the learner's own mixture
  supermartingale — `confidence_step_pow_four`, `sum_inv_fourth_le_two`
  (`LeanPaperAConfStepV1`); `a7_chain_rate_constructed` is the chain with `hstep` removed.
* the code's three accumulators ARE the model's — `Wcode_eq_W`, `Ncode_eq_visits`,
  `Scode_eq_sum_visits`, `mixed_allocation_floor`, `code_count_growth`
  (`LeanPaperAIdentifyV1`).
* **the threshold hypothesis was false for the implementation and is now repaired rather
  than renamed.** `thr_n = log(1/α) + ½Σ_e log(1+N_e(n)/a)` is unbounded in `n`, so
  `a7_chain_rate`'s `hthr` never applied to the code. `code_threshold_sublinear` bounds the
  growing term by `κn + C_κ` for every `κ>0`; `a7_chain_rate_code_threshold` runs the chain
  on `Z_n − κn` against `thr_n − κn`, which leaves the crossing event unchanged and costs
  `G → G−κ`; `rate_limit_as_kappa_to_zero` makes the loss arbitrarily small
  (`LeanPaperA7ThresholdV1`).

**Supporting, not headline.** The region oracle's covering (`unsafe_iff_union_of_polyhedra`)
and its two traps; the exact one-step martingale (`one_step_is_equality`); the freezing
lemma (`condExp_freeze`).

---

## Paper B — how far you must observe to decide, not to identify

**Model, fixed once.** A finite world family with safe-answer sets `A_θ`; an admissible query
class; densities `p^q_{θ,h}` expanded in the perturbation scale `h`; resolving order
`r(θ,λ)` the first order at which some admissible query separates the pair.

| # | Status | Headline | Final theorem (module) | Construction | Evidence | What it still takes |
|---|---|---|---|---|---|---|
| B-H1 | **headline; the channel link now proved** | The safe order is the geometry's: `s_safe` is the largest, over unsafe subsets, of the smallest resolving order inside the subset | `safeAt_iff`, `safeAt_zero_of_no_unsafe` (`LeanPaperBSafeOrderV1`); on the channel `resolveOrder_is_least`, `resolving_order_finite`, `resolving_order_attained` (`LeanPaperBQueryClassV1`) | stated over all unsafe subsets | — | `resolveOrder` was written as `min w w'` and the derivation from the observation law was missing. It is now proved: `query_separates_iff` makes the set of separating queries `{w, w'}`, and `resolveOrder_is_least` states `IsLeast` of that set — the smallest separating order, not a definition adopted by fiat |
| B-H2 | **partly closed** | The per-step divergence is `≤ C h^{2r}` uniformly over the admissible query class | `kl_uniform_over_queries`, `chi2_uniform` (`LeanPaperBWorldsV1`); box discharged on the channel by `channel_kl_uniform` (`LeanPaperBQueryClassV1`) | `P = 2^{-r}Σ_z(1+parity z)M(·−v z)`, `Q = 2^{-r}Σ_z M(·−v z)` | — | **closed on the chi-square side**: the identity `p₊ − p₋ = D_{b₁}…D_{b_r}[φ(·−1) − φ(·+1)]` (`channel_pair_diff`), the componentwise envelope and the resulting bound with its factor four (`pair_envelope`, `pair_chi2_bound`), and the normalisation of the unnormalised `gkern` (`gkern_integral`, `kl_scale`, `chi2_scale`, `LeanPaperBPairRateV1`). `paperB_uniform_hellinger.json` is evidence for the abstract family, not for the decoder's pair, and is no longer cited as if it were. `hkl`, `henv`, `hint`, `hmass` remain |
| B-H3 | **closed for the paper's channel** | The transcript bound holds for any adaptive policy | finite alphabet, fully constructed: `Lr`, `martingale_step`, `change_of_measure`, `expect_Lr_eq_one`, `kl_chain_le_horizon`, `parity_channel_transcript` (`LeanPaperBTranscriptV1`); abstract continuous form `kl_le_horizon` (`LeanPaperBChangeV1`) | the likelihood ratio along the realised history, for ANY `π : List Y → K` | — | the continuous-alphabet module still takes `hdens` and per-step `klIncr`; building those from a Gaussian policy's kernel is open |
| B-H4 | **upper side closed in `δ`; rate curve not measured** | The two exponents separate, and the separation is an identity | `separation_ratio`, `separation_unbounded` (`LeanPaperBHeadlineV1`); upper side `log_budget_suffices`, `budget_at_scale`, `sides_match_in_delta` (`LeanPaperBHoeffdingV1`); union over `J` tests `union_budget_value`, `union_error_le` (`LeanPaperBScopeV1`); exact lower constant `lower_budget_exact`, `kl2_ge_of_ratio` (`LeanPaperBExactConstV1`) | the parity-mask channel; `A_w = [m]∖{w}` | `paperB_decoder.json` | the empirical identification-rate curve: 7 of 8 identification cells are censored, so only one `(m,h)` compares both decoders. The measured ratio is a ratio of budgets meeting a ladder standard, not a measured complexity ratio |

**Two corrections recorded rather than left standing:**

* **Hoeffding is in Mathlib on the current pin.** The earlier note that it was absent, and
  the resulting stop at Chebyshev's `1/α`, were wrong.
  `hasSubgaussianMGF_of_mem_Icc` and `measure_sum_range_ge_le_of_iIndepFun` give
  `Pr(error) ≤ e^{−Ng²/8}` for a statistic in `[−1,1]`, hence `N ≥ 8log(1/δ)/g²`, and
  `sides_match_in_delta` bounds the ratio of the two sides by a constant free of `δ`.
* **`self_difference_not_a_density` is about ONE first difference.** It refutes the
  composition that was in use; it does NOT say `q + D_{b₁}…D_{b_r}q` fails at every order.
  At order two the object is a density whenever `q` is —
  `q + D_sD_sq = q/2 + q(·−2s)/4 + q(·+2s)/4` — which is `second_difference_shape` and
  `second_difference_nonneg` (`LeanPaperBScopeV1`). The retraction stands at first order;
  the overstated scope does not.
* **The lower bound's loosened constant can be negative.** `cDelta K δ` at `K=4, δ=0.05`
  is about `−0.0243`, so `lowerBudget` certifies nothing there and `δ < 1/m` does not repair
  it. Keeping the binary divergence exact gives about `0.2024`.
  `exact_dominates_loosened` shows the exact constant is never smaller, and
  `kl2_ge_of_ratio` shows it is at least `δ` once `e·δ ≤ (1−δ)/K` — at `K=4` that is
  `δ ≤ 1/(1+4e) ≈ 0.0842`, so `δ = 0.05` is inside it.

---

## Paper C — the price of serving one ranking across every budget

**Model, fixed once.** The signed-prefix family `g_m = (−3, −1×p, +1×q, +3)`, normaliser
`D = m+4`; a law over rankings; regret `r_k = (|S_k| − b_k)/D` with `b_k = k mod 2`;
objective `max_k E r_k`; retained-prefix band `|Pr(i ∈ prefix_k) − k/m| ≤ η/m`.

| # | Status | Headline | Final theorem (module) | Construction | Evidence | What it still takes |
|---|---|---|---|---|---|---|
| C-H1 | **two-sided at even `m`; one construction owed** | The exact value at uniform marginals: `4/m(m+4)` at even `m`, `(m+3)/m(m+4)` at odd `m` | value: `evenMixture_value_at_D` (`LeanPaperCMixV1`), `winValue_le`, `winValue_at_last` (`LeanPaperCValueV1`); flipped value `insMixtureEven_free_value`; **feasibility at `η = 0`**: `uniformMix_heavy`, `uniformMix_light`, `uniform_band_zero` (`LeanPaperCUniformV1`) | insertion mixture + the flat ranking at weight `1/m`, each mixed with its sign flip; uniform cyclic rotations (odd) | `paperC_window.json` | **the value is now pinned from both sides** — the lower side is the budget-1 identity `E r₁ = 4/(mD)`, holding for EVERY law feasible at `η = 0` (`value_ge_at_uniform_at_D`, `Vm_ge_at_zero`, `Vm_eq_at_zero`, `LeanPaperCLowerZeroV1`). What `Vm_eq_at_zero` still asks for is ONE feasible law of that value: the index set, the law and the permutation family. Every ingredient is proved; the construction is not written. **An earlier version of this row said "exact value" on an upper bound alone; that was an over-claim I found while checking my own work.** Two further corrections on this row. (i) **The feasible set itself was empty and the lower side was therefore vacuous.** `FeasibleAt` (`LeanPaperCValueSetV1`) quantified the band over all `k : ℕ`; at `k = m+1` the left side is `1` against `k/m = 1 + 1/m`, so no law was feasible at any finite `η` and `Vm_ge_at_zero` / `Vm_eq_at_zero` said nothing. The quantifier is now bounded to `k ≤ m` and the set is proved **inhabited** — `cyclicPerm` / `cyclicLaw` / `cyclic_marginal` / `feasible_zero_nonempty` exhibit the uniform law on the `m` cyclic shifts, whose retained marginal is exactly `k/m`. This was my own defect, introduced in this corpus and found in it. (ii) **The band `hband` is no longer assumed**: `LeanPaperCRelabelV1` derives it from the weight-preserving relabelling (`band_zero_of_relabelling`), and its own hypotheses are discharged concretely by `WPerm` / `wperm_inv` / `wperm_trans` / `wperm_orbit`, so they are shown satisfiable rather than asserted. **Still open:** `band_zero_at_weight_group` takes the per-weight-class occupancy `hclass`, not yet discharged for the concrete even-`m` mixture, and `witness_for_Vm_eq_at_zero` (`LeanPaperCPermV1`) still takes `hvalue` |
| C-H2 | **two-sided; the earlier "tension" was my error and is withdrawn** | The breakpoint is two-sided at every `m`: `η_* = 1` (odd), `(m−2)/2(m−1)` (even) | lower: `O2_even_at_ranking_law` (`LeanPaperCEndpointV1`), `O2_strict_odd/even`; band and value of the mixture: `O1_odd`, `O1_even`, `insMixtureEven_free_value` (`LeanPaperCRankingV1`) | `g_m` written down, heavy set computed | `paperC_general_m.json` | **withdrawn.** I flagged a possible contradiction with the `η = 0` mixture. There is none, and the retraction is a theorem: the flat-augmented mixture attains `4/(mD)`, while `breakpoint_lower_even`'s hypothesis is the strictly smaller free value `2/(D(m−1))`, and `free_value_lt_uniform_value` separates them at every `m > 2` (`LeanPaperCEvenResolveV1`). The breakpoint stands as stated |
| C-H3 | **headline on the naming side; the path-decomposition half RETRACTED** | A ranking law's objective transports to its own flow, budget by budget — every budget's value at once, not one aggregate | `budget_vector_transports`, `objective_transports` (`LeanPaperCNamingV1`) — unaffected. **`pathDecomposition_count_states` (`LeanPaperCFinalV1`) is withdrawn**: its domain is empty | observables named at `rankLayer ty k`; the repaired domain is `CountFeasibleH` with the explicit flow `horizonFlow` (`LeanPaperCHorizonV1`) | `paperC_flow_lp.json` — **flagged, not removed**: it is an LP over the flow polytope, cited on a row whose path-decomposition theorem is withdrawn, so it is evidence for an object the retracted half no longer reaches | **`CountFeasible` (`LeanPaperCFinalV1`:146) has no unit flow at all** — it demands a legal one-item step at EVERY layer `k`, while the served count `R(v) = Σ_τ v_τ` is bounded by `d·m` and conservation forces `E[R(V_{k+1})] = E[R(V_k)] + 1`; at `k = dm+1` those contradict. That is now a theorem, `countFeasible_empty` (`LeanPaperCVacuityV1`), not a remark. So `pathDecomposition_count_states` is a conditional with unsatisfiable hypotheses and proves nothing; the same holds for `pathDecomposition_at_count_states`, and the whole of `LeanPaperCPathV1` — its `NoRelabel` / `secOf` / `hsec_secOf` results are stated over that empty domain. The repair carries its own non-emptiness proof and is recorded below. **What this row must NOT be read as saying:** that the ranking problem and the flow problem have the same optimum. Nothing in the gated corpus proves it. `budget_vector_transports` and `objective_transports` move ONE law's objective to ITS OWN flow; they do not compare the two feasible sets. An earlier version of this row said "ranking ⇄ flow … hence the maximum and the optimum" and carried "and repaired" in its status, which together read as a closed reduction and contradicted this row's own footnote below; both are withdrawn. Per-item band constraints still need the relabelling route (`per_item_from_flow`) |
| C-H4 | **headline** | Robustness has an exact reach: at `ε ≤ 1/2m` the linear price survives; at fixed `ε` the same bound certifies nothing linear | `ratio_linear_at_small_eps`, `ratio_bounded_at_fixed_eps` (`LeanPaperCTransport2V1`) | weight perturbation with `D` and the feasible set held fixed | `paperC_perturbation.json`, `paperC_robustness.json` | **the collapse scale is now located**: `ratio_collapse_lower` gives the matching lower bound `(1/8)·min(m−1, 1/ε)`, so the order is `min(m, 1/ε)` from both sides and the crossing is at `ε_c = 1/(m−1)` (`LeanPaperCCollapseV1`). Band relaxation at fixed `η` is a different result and is still not combined with this one |


**Retracted this round, and repaired in the same round (Paper C's flow side).**

*The retraction.* `countFeasible_empty` (`LeanPaperCVacuityV1`) proves `CountFeasible ty F →
False`. The gate stayed clean throughout, because a conditional with contradictory hypotheses
is still a theorem — which is exactly the failure this table exists to catch. Withdrawn, as
statements about flows: `pathDecomposition_count_states` (`LeanPaperCFinalV1`),
`pathDecomposition_at_count_states` (`LeanPaperCPathV1`), and every result of
`LeanPaperCPathV1` that is stated over that domain (`NoRelabel`, `secOf`, `hsec_secOf`). The
`hsec` machinery underneath them — `hsec_count_states`, `matchPerm`, `legal_path_realised`,
`countSec_layer` — survives; what is retracted is that any flow satisfies the premise.

*The repair, with non-emptiness PROVED rather than asserted.* `LeanPaperCHorizonV1` defines
`CountFeasibleH`: legality only while `k < m`, self-loops afterwards, plus the LP's own
capacity constraint `v_τ ≤ mult ty τ`. On that domain `start_empty` and `end_full` — which the
old definition took as **hypotheses** — are DERIVED, from `served_grows_H`, `served_le_m`,
`expected_served_zero` and `mult_sum`. And the domain is proved inhabited: `horizon_flow`
exhibits the explicit deterministic flow `horizonFlow`, which serves the items in index order
and then idles, with `cnt`, `cnt_le_mult`, `cnt_succ`, `stC`, `stC_step`, `stC_idle` the
supporting lemmas. The point of the repair is that the new domain is not empty *and this is a
theorem*; the mistake is not repeated in the other direction.

*Not yet done.* The retracted path-decomposition results have not been restated over
`CountFeasibleH`; `trajLaw_stepC` and the section need finite-horizon versions before they
can be.

---

## Experiments

| Artifact | Status |
|---|---|
| `paperA_swap.json` | **statistic corrected and reporting split.** The certificate now uses the martingale's own weight `N²/(a+N)` rather than `N`; the old weight inflated the statistic, so the `α`-guarantee did not apply to it. Runs are counted as `stopped_correct` / `stopped_wrong` / `censored`; the earlier "576/576 correct" counted horizon estimates of censored runs. The panel is a fixed-allocation certificate test and does NOT exercise A7's sticky selection or oracle tracking. At `M = 1` the "geometry" and "uniform" allocations are the same vector, and the run now checks and says so |
| `paperA_mechanism.json` | **regenerated with the corrected statistic** `effective_N = N²/(a_reg + N)` (`scripts/EXP_paperA_mechanism.py`), the martingale's own weight rather than `N`; the run passes 5/5 self-checks. **The proxy rule is censored at every `r`** — 24/24 runs censored and `correct = 0/24` at `r = 1, 2, 4, 8` — so what is tabulated for it is the restricted mean `E[min(τ, B)]` with the censored count printed beside it, NOT absorbed into a mean. One of the five checks is that this reporting split holds |
| `paperB_decoder.json` | **confidence corrected.** The reported budget is the first rung of a 7-rung ladder that clears the target, so every Clopper–Pearson interval in the run is taken at level `1 − 0.05/J` with `J = 392`. Certified cells: 9 uncorrected, 9 panel-corrected, 9 family-corrected; two budgets move under the family correction (`m=3, h=0.6` safe 25→50; `m=3, h=0.32` safe 50→100). Only ONE `(m,h)` has both decoders certified, so there is no identification-rate curve here |
| `paperC_window.json`, `paperC_general_m.json` | unchanged |

---

## How to read a status

**headline** — a final theorem on the paper's own object, taking no hypothesis that is the
conclusion. **conditional** — the algebra is proved but a hypothesis carries part of the
conclusion; the hypothesis is named in the last column. **partly closed** — some links
proved, others named. Nothing in this table is upgraded because an audit count rose.
