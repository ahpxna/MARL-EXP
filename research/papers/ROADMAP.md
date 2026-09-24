# Completion roadmap — state of every named deliverable

The supervisor's roadmap of 2026-09-21, item by item, with what is actually closed. Four
statuses, and they are not interchangeable:

| | meaning |
|---|---|
| **LEAN** | proved in Lean, no uninstantiated hypothesis, axioms `{propext, Classical.choice, Quot.sound}` |
| **LEAN-COND** | proved in Lean but consumes a hypothesis that is not discharged at the paper's own construction |
| **NUM** | measured by a self-checking script; an artifact, not a theorem |
| **OPEN** | not done — including "argued in prose" |

## Corpus state at the last full gate

```
last completed FULL gate   full3_20260924_ideal    finished 2026-09-24 12:44
modules = 188 (listed 173)   audited_theorems = 1505   failed = 0
sorry = 0   native_decide = 0   axioms ⊆ {propext, Classical.choice, Quot.sound}
VERIFY PASS   (drift note: LeanPaperCCollapseV1 was edited after that freeze -- docstring
               only, the SCOPE paragraph; the verdict is about the frozen bytes)
proof hashes: work/gate_runs/full3_20260924_ideal/report/MODULES.tsv (per-module source
  and .olean sha256), SOURCES.sha256, RUNNER.sha256.  sha256(MODULES.tsv) =
  979d9703cf217b5f17b70a36bde438991557d849650ae124835909a6d13b4f23
previous FULL gate         full2_20260923_201950   143 modules, 1293 theorems, PASS

latest SMOKE gate          smokeA_20260924_ideal   finished 2026-09-24 09:16
closure of LeanPaperA7IdealFamilyV1: modules = 54   audited_theorems = 431
failed = 0   sorry = 0   native_decide = 0   axioms ⊆ standard   drift = none
SMOKE PASS

running SMOKE gate         smokeA6_20260924        closure of the three A6 modules
                           (LeanPaperA6FixedDesignV1, LeanPaperA7StoppedGenV1,
                           LeanPaperA6SurrogateCostV1); not in full3
```

## One observation that shortens what is left of C

The odd family's prefix sequence takes only **three** values, in a completely regular
pattern. With `base = (+3, −3, −1, +1, −1, …, −1)` and `m` odd,

```
P₀ = 0,   P₁ = 3,   and for j ≥ 2:   Pⱼ = 0 if j is even,  −1 if j is odd,
```

so in particular `P_m = −1`, which is the total. A circular window `[a, a+k)` has sum
`P_{a+k} − P_a` when `a+k ≤ m` and `total − P_a + P_{a+k−m}` otherwise — and since `P` takes
values in `{0, 3, −1}` only, the classification of circular windows that the remaining
budgets need reduces to **finite arithmetic on three values with a parity index**, not to a
combinatorial census. The critical budget `k = m−1` is already closed without it
(`sum_rot_abs_prefix`, `LeanPaperCOmitV1`); this is the route for the rest.

A theorem that takes a hypothesis is **not** the headline until that hypothesis is
instantiated at the construction or algorithm the headline is about.

---

## Paper A

| Item | Status | Where | What remains |
|---|---|---|---|
| **A1** one model for construction, KL and oracle | **mostly LEAN** | `Centred`, `FrozenAltC₀`, `TrueAltC₀`, `frozenGameC₀_eq`, `centred_ratio₀_le` (`LeanPaperACentredV1`); and the general links already exist: `residual_eq_inner`, **`loss_eq_half_range`** (the loss *is* half the range of a linear form), `selectedRadius_eq_compressionLoss` (`LeanPaperAModelBridgeV1`, 18 thms) | **done** in `LeanPaperACentredModelV1` (20 thms): `centred_iff_marginals` characterises `Θ₀` as *exactly* the class where both uniform-product marginals recover their coordinates; `residA_eq` + `rangeB_eq_osc` + `lossRetainA_eq` give `L_λ(\{A\}) = range(λ_B)/2`; `unsafeA_iff_range_gap` gives the decision with its tolerance and **strict** sign. **both now closed** (`LeanPaperAStrictV1`): `energy_eq_sum_gaussKL` gives the divergence for *every* candidate, and the **strict** game is defined with both bounds and starvation transferred |
| — both games restricted to one `Θ₀` | **LEAN** | `frozenValueC_le_restricted` states the direction (restricting *raises* an infimum), `lamStar_mem_centred`, `pairShiftC_mem_centred` | — |
| **A2** separation, upper side `Γ_true ≤ 1/(8rM)` | **LEAN** | `trueGameC₀_le` | — |
| **A2** `Γ_fr = 9/512` exactly | **LEAN** | `frozenGameC₀_eq` | — |
| **A2** lower side `Γ_true ≥ 9/(128(4+2rM))` | **LEAN** | `wCert`, `energy_wCert`, `contrast_movesC`, `trueValueC₀_wCert_ge`, `trueGameC₀_ge` | — |
| **A2** the two-sided ratio `4/(4+2rM) ≤ Γ_true/Γ_fr ≤ 64/(9rM)` | **LEAN** | `centred_separation` | — |
| **A2** strict boundary by real alternatives | **LEAN** | `pairShiftC_strict_alt` — for every `δ>0` the shift by `1/2+δ` is strictly alternative *and* centred | — |
| **A3** starvation ⇒ the surrogate's design is uninformative | **LEAN** | `starvation_at_optimum₀`, `near_optimal_starvation₀`, `frozen_optimum_trueValueC₀_zero`, `near_optimal_trueValueC₀_le` (`J_true ≤ 64ζ/(9rM)`) | — |
| **A6** the repair frontier `F(β)` | **LEAN** | `value_concave`, `frontier_upper`, `frontier_lower`, `frontier_two_sided`, `frontier_at_zero` (`LeanPaperAFrontierV1`) — `9β/(128(4+2rM)) ≤ F(β) ≤ β/(8rM)`, i.e. `Θ(β/(rM))`, with the mixture `w_β = (1−β)w_unif + βw_cert` explicit | — |
| **A5.1** the one-step identity | **LEAN** | `shift_integral`, `one_step_mean`, `one_step_is_equality` (`LeanPaperAMartingaleV1`) — an **exact** martingale, by one Gaussian integral; no continuous-prior Tonelli | **all five now discharged.** Measurability: the bookkeeping in factorised form plus `Mstep_measurable`. Conditional law: independence on the stream. Random past: a **freezing lemma built from `condDistrib`** (`LeanPaperAFreezeV1`) — Mathlib has none — applied with `one_step_mean` inside (`martingale_step`). `E M_t = 1` **and integrability**, the latter *derived* by the product criterion rather than assumed (`joint_integrable`). Ville: `Mval` **is** `Mstat` by `rfl`, the crossing forces `M_t ≥ 1/δ` because the penalty cancels, and the one-step equalities assemble into a Mathlib `Martingale` (`LeanPaperAStopJoinV1`). Still owed: identifying the code's `q_t, N_e, S_e` with the model's |
| **A4** covering, from the actual compression loss | **LEAN** | `unsafe_iff_union_of_polyhedra` (`LeanPaperARegionV1`): `Unsafe(ε)` **equals** a union of polyhedra, each cut by two linear inequalities, both inclusions, via A1's `unsafeA_iff_range_gap` | — |
| **A4** the rest of the oracle | **partial** | closure exchange `LeanPaperClosuresV1`; weak-duality lower / LP upper and the zero-weight floor in `EXP_paperA7_learner.py`; and an **exact closed-form** regional bound on the centred family in `EXP_paperA_mechanism.py` (verified against a constrained solver to `2e-16`) | **closure validity is now LEAN** (`lower_bound_transfers`, `LeanPaperAOracleRegionV1`): the segment from a strictly bad point transfers lower bounds from the strict region to its closure, and a region with an empty strict part is dropped. Zero weights are handled (`objective_indep_of_zero_weight`). Still owed: the outer certificate bounding every design |
| **A5.1** the mixture route | **superseded** | `adaptMix_supermartingale`, `mixture_closed_form` (`LeanPaperA7StreamV1`) remain as the finite-mixture statement | the continuous-prior transfer is no longer needed: the closed form is proved an exact martingale directly |
| **A5.2** oracle stability in value | **LEAN** | `J_lipschitz_in_world` (`LeanPaperA7OracleSelectV1`) | constants carrying `1/σ_min²` explicitly |
| **A5.3** sticky selection keeps an information-optimal answer | **partial** | selection rule checked on constructed inputs (`EXP_paperA7_learner.py`, 108 cases) | the elimination statement at the algorithm's own confidence set |
| **A5.4** tracking from the recursion | **LEAN** | `LeanPaperA7TrackingV1` | — |
| **A5.5** accumulated information → stopping statistic | **LEAN**, and joined to the rest | `good_window_accumulation`/`good_window_rate` give `Z_t/t ≥ Γ − 3Lr̄ − ē − Γρ̄ − 2Γn/t − C/t`; `LeanPaperA7ChainV1` composes it with the inclusion, the tail and the expectation | `ξ_t` (stopping solver) is still a *separate* error from `ζ_t` (allocation oracle), and neither is instantiated at the implementation |
| **A5.6** tail, a.s. termination, expectation | **LEAN-COND; the `∞`-valued stopping time is now LEAN** | `expected_stopping_bound_general`, `rate_limsup_eta` (`LeanPaperA7EtaV1`) still consume the expected bound; `hitTime`/`truncAt` (`LeanPaperAStoppingV1`) give the `ℕ∞`-valued hitting time, its tail event, and the separation between the restricted quantity and the stopping time | **closed**: `chain_expected_bound` (`LeanPaperA7ChainV1`) derives `E τ ≤ (b + winBudget)/((1−ε)Γ) + 19` from the algorithm-level hypotheses, and `a7_chain_rate` feeds it to `rate_limsup_eta`. Joining the links exposed the window head — the crossing time is `b/G + O(√b)`, not `b/G + O(1)` — paid by `2Γ√t ≤ εGt + Γ²/(εG)` at the cost of a factor `(1−ε)` of the rate. The `s^{-4}` confidence step is still a hypothesis |
| **A6** surrogate learner `Ω(log²(1/α))` | **assembled** | `surrogate_cost_quadratic`, `surrogate_omega_log_squared`, `separation_diverges` (`LeanPaperASurrogateV1`): Jensen on the square-root exploration budget plus `kl2_ge_log` gives the quadratic in `log(1/α)` | the stopped change-of-measure at a hidden pair is an input (`hchange`); supplying it for the concrete policy is what separates this from an algorithm-level claim. The swap panel (`paperA_swap.json`) measures the mechanism |
| **A6′** tracking an exact surrogate optimum, `Ω(log²(1/δ))` | **LEAN (2026-09-24), oracle-allocation** | `surrogate_optimum_cost`, `surrogate_vs_ideal`, `starved_cost_log_sq`, `starved_lower_at`, `klq_pair`, `surrogate_optimum_exists`, `uniform_surrogate_cost` (`LeanPaperA6SurrogateCostV1`); `fCount_le_amgm` (`LeanPaperA6FixedDesignV1`); `cnt_eq_at_min` (`LeanPaperA7StoppedGenV1`). `E τ_δ ≥ (KM/8)² log²(1/δ)` for the DEFINED learner (warm start, `1/√(s+1)` forcing, `argmax(s w⋆ − N)`, true GLR stop), for EVERY exact frozen optimum `w⋆`; ratio to the ideal learner unbounded | the design is the surrogate optimum AT THE TRUE WORLD, fixed: the true extrema enter the allocation. A learner recomputing the surrogate at its estimate is still open (the A6 row above, cumulative-exploration route) |
| **A7-II** the IDEAL learner, end to end: exact rate `1/Γ_actual` on the family | **LEAN** (2026-09-24; smoke gate `smokeA_20260924_ideal` PASS, 54 modules) | `ideal_family_finish` (`LeanPaperA7IdealFamilyV1`): `OperationalFinish streamMeasure (δ ↦ tauI famSpec a δ θC) (actualKLGame r M)` with NO hypothesis beyond `M>0`, `r>0`, `a>0`. Upper: `ideal_expect_bound`/`ideal_upper_rate`/`ideal_finite` (`LeanPaperA7IdealUpperV1`) from `ideal_direct` (`LeanPaperA7IdealDirect2V1`, box-free accumulation on the good window), `good_window_real` (Ville at the learner's own statistic, `s^{-4}`) and `expect_le`. Lower: the stopped learner on `Cell ⊕ Unit` (`LeanPaperA7IdealStoppedV1`: `runS_eq` pathwise coupling, `cnt_le_tau`, `ansEv_alt_le`, `ansEv_true_ge`) + `stream_eq_hist_fresh` + `family_policy_lower` at level `2δ`, horizon by Markov (`ideal_family_lower`, `lower_rate_of_bound`). `GamT_fam`: the learner's game IS `actualKLGame`. Correctness: `ideal_correct`/`ideal_family_correct` | **Scope.** The learner is IDEAL (reviewer spec §A.5 "exact asymptotic theorem"): its oracle maximises the exact value `J` over a refining ε-net (mesh `1/(s+1)`) and its stop is the exact GLR infimum, so `ν_t = 0` by construction. It is not the shipped learner: `EXP_paperA7_learner.py` (1e-6 floor, 80-iteration cap) is Theorem I's finite-precision algorithm and its rate stays conditional. No numerical artifact was produced by this learner |
| A panel, per `α`, common random numbers | **NUM** | `paperA7_learner.json`, 22/22 checks, hash-matched | — |
| A-F1 + A-F2: the centred separation interval and the allocation mechanism | **NUM + THEOREM, drawn 2026-09-24** | `paperA_mechanism.pdf` (`FIG_paperA_mechanism.py`, 7/7, from `paperA_mechanism.json` only; nothing re-solved). Interval: attained float LOWER certificate up to the theorem's upper bound; at `r=8` it lies below 1 | **scope, from the audit** (`paperA_mechanism.PROVENANCE_NOTE.md` addendum): the stop certifies answer A only, so these runs are an allocation diagnostic under one certificate, not δ-correct learners. A numerical UPPER bound for `Γ_true` (a model-aware producer with centring) is not built |
| A slope along the `α` axis | **NUM** | `paperA7_alpha_slope.json`, 4/4 checks | — |

### Supervisor decisions on the eight proposed proof routes (2026-09-22)

| # | Proposal | Decision |
|---|---|---|
| 1 | direct Gaussian martingale for the closed form | **adopt**, plus measurability / random-past conditional identity / integrability induction |
| 2 | prove the C endpoint identity | **use the existing** `two_budget_identity`, `two_budget_identity_div`, `hid_for_breakpoint` — do **not** re-prove; do the actual-family instantiation |
| 3 | max over **all** unsafe subsets | **adopt**, keep minimal-obstruction characterisation as a corollary; handle the two edge cases (no unsafe subset; a pair never resolved) |
| 4 | B7 as a corollary of B2 | **only after** the density-derived resolving-order table is closed; B2 does not prove that table |
| 5 | index tests by class | **adopt only with a uniform composite-test lemma** — a test between two representatives is not a test between two classes |
| 6 | likelihood-ratio martingale replaces the transcript proof | **amended, and now done**: `L_t = dP_θ\|_{F_t}/dP_λ\|_{F_t}` and the KL chain rule are proved in `LeanPaperBChangeV1`; the martingale property appears as `condExp_L`, derived from consistency rather than assumed |
| 7 | `P² = 1` for the cube block | **adopt** — and it holds for every `r`, which a numerical check cannot give |
| 8 | `Θ₀` by the marginal `iff` | **adopt the iff**; a definition does not replace the loss/unsafe equivalence or the strict-boundary proof |

---

## Paper B

| Item | Status | Where | What remains |
|---|---|---|---|
| **B-END** (current state, 2026-09-24) both minimax rates on ONE channel | **LEAN, unconditional on the parity channel** | `parity_tip_finish`/`parity_rates` (`LeanPaperBParityFinishV1`): for every `m≥3`, `σ>0`, over every randomised adaptive policy with a FINITE horizon, minimax cost `Θ(log(1/δ)/h²)` (safe) and `Θ(log(1/δ)/h^{2(m−1)})` (identification), uniform on a rectangle in `(h,δ)`; lower sides `safeLower`/`idLower`, upper sides `safeCert`/`idCert`. Decoder data vs formalized decoder: `lean_wrong_imp_py_wrong` (`LeanPaperBDecoderMatchV1`) + `paperB_decoder.PROVENANCE_NOTE.md`. In the manuscript as Theorem `thm:endpoint` (2026-09-24) | the `F_{u,v}` linear-probe family of §family: adaptive Gaussian instantiation and identification-rate curve still open; policies with unbounded (a.s. finite) stopping times are outside the class. The "what remains" entries of B1–B8 below are HISTORY where they concern the parity channel |
| **B1** fixed-budget worst-case theorem as the headline | **half LEAN, and the halves are separated** | `budget_lower` (`Ω(h^{-2s} log(1/δ))`, constant free of `h` and `δ`), `safe_upper` (Chebyshev, `O(h^{-2}/α)`), `separation_ratio` (an **identity**: `lowerBudget(t+1) = (36αc_δ/CV)·h^{-2t}·safeSufficient`), `separation_unbounded`, `sides_do_not_match` (`LeanPaperBHeadlineV1`) | the two sides do **not** match in the confidence parameter — `log(1/δ)` below, `1/α` above — so `N* = Θ(h^{-2s} log(1/δ))` is **not** a theorem here and must not be written as one. Closing it needs the exponential-in-`N` test of §B2c |
| **B2** observation order from the density | **partial, and one error corrected** | `LeanPaperBIndistV1`: `indistAt_iff_no_separating_query` — the partition is derived from an explicit **coefficient table**, both directions. The table was called a *moment* table; read as raw moments it is **not realisable by any law** (world `0` would need `E X = 1`, `E X² = 0`). It is now labelled as expansion coefficients in `h`, which is what B2 needs | **the table is now realised by actual densities** (`LeanPaperBDensityV1`): `dens i h = (1−h^{i+1})φ + h^{i+1}φ(·−1)` is a genuine density whose `h`-expansion coefficient is `coefOf i k` times one profile, and the resolving order `r(i,j) = min(i,j)+1` is derived from those densities in **both** directions. The formula itself is `safeAt_iff` (`LeanPaperBSafeOrderV1`), over *all* unsafe sets. Still owed: that the parity-mask construction's own densities have these coefficients |
| **B3** KL upper bound uniform over the query class | **chain complete but for ONE identification** | `kl_integrand_le`, `kl_le_envelope` (`LeanPaperBKLV1`): `KL ≤ ∫(p−q)²/ℓ` for any floor `0 < ℓ ≤ q`, via `log x ≤ x−1`; and `hellinger_integrand_le_chi` records why a Hellinger bound alone cannot do it | **the identification is closed, and its old form is retracted.** `self_difference_not_a_density` (`LeanPaperBWorldsV1`) proves the previous `hdiff` — `p − q = iterDiff q shifts` with `p ≥ 0` — is *contradictory* at any nonzero shift, so that composition was vacuous where it mattered. `worlds_diff` replaces it with an identity for a constructed pair `(P,Q)`; `worldQ_floor` + `mixDens_floor` give the floor; `chi2_uniform` needs **no** integrability hypothesis and `kl_uniform_over_queries` carries two, both properties of the pair. The constant `klConst(σ,R,h₀,r)` mentions no query. Still owed: that a given observation model's queries *induce* shifts inside the box |
| **B4** one query → adaptive randomised transcript | **algebraic core LEAN, now for ADAPTIVE policies** | `policy_cancels_adaptive`, `weightH_common_factor`, `log_weightH_ratio` (`LeanPaperBAdaptiveV1`): the kernel may read the **whole** transcript and still cancels, with no predictability used; `LeanPaperBTranscriptV1` is the fixed-kernel case | the measure-theoretic half is now closed (`LeanPaperBChangeV1`): `change_of_measure`, `setIntegral_L_succ`, `condExp_L` (the tower property), `kl_eq_sum_increments`, `kl_le_horizon` — no finite alphabet, and the policy never appears because it sits inside the filtration. Still owed: that a concrete adaptive Gaussian policy's transcript law *admits* such an `L_t`, built from its own kernels |
| **B5** attainment by characteristic functions | **cube half LEAN** (`cube_sum`, `cube_difference`, `LeanPaperBCubeV1`) — exact for every `r`, via `P²=1`; rest open | `PROOFS.md` §B2c — the identity is derived and matches a brute-force cube sum to `1.3e-16` at `r∈{2,3,4}`, fitted orders `2.000/3.000/4.000` and head `1.000` | formalise: the identity `φ₊−φ₋ = 2i sin t cos 3t cos²2t e^{-σ²t²/2}(i sin(th/r))^r`, then a bounded test `cos(t₀Y)`/`sin(t₀Y)` and Hoeffding — avoids the high-variance `Y^{r+1}` estimator entirely |
| **B6** decoder for the safe decision | **skeleton LEAN** | `composite_test_separates` (uniform over each class, no representative), `separation_of_gap`, `decoder_output_exists`, `decoder_is_safe_at_truth` (`LeanPaperBDecoderV1`) — built **on** `SafeAt`, so the output is guaranteed to exist | candidate elimination, `θ_true ∈ C_N ⊆ [θ_true]_{∼s_safe}`, output from `⋂_{λ∈C_N} A_λ`, and the **total** query budget |
| **B7** the tip/parity-mask construction (`m≥3`) | **loss half LEAN, on the real `selectedRadius`** | `selectedRadius_self`, `selectedRadius_other`, `safe_iff_ne` (`LeanPaperBTipV1`) compute the safe sets **from the compression loss**; `coSafe_*` (`LeanPaperBSafeOrderV1`) give the law's geometry | `selectedRadius_w(\{j\}) = (m−1)/2` iff `j=w`, so `A_w = [m]∖\{w\}`: pairwise intersecting, empty total intersection; `s_safe=1`, `s_id=m−1`; and `δ` must be below the zero-query minimax floor `1/m` |
| **B8** figures and numerical fixes | **partial** | Hellinger via `(p−q)²/(√p+√q)²`; canonical tail probe seeded; search limits recorded | figures for the new decoder and construction |
| B evidence classes kept apart | **done** | scope block in `paper_b.tex` | — |

## Paper C

| Item | Status | Where | What remains |
|---|---|---|---|
| **C-END** (current state, 2026-09-24) both endpoint laws, the flow program, the physical objective, stability | **LEAN, unconditional** | `even_frontier_all` (every even `m≥4`), `odd_breakpoint`/`oddBreakpointFinish_holds` (every odd `m≥3`), `odd_value_zero`, `even_value_zero`; `value_eq_flow`, `even_frontier_flow`, `odd_breakpoint_flow` (`LeanPaperCFlowObjectiveV1`); `familyBaselineIdentification_holds` (`m≥3`), `trueValue_family` (physical value = paper's value); `trueValue_stable`, `family_value_robust`, `even_frontier_robust` (`3‖g−g'‖₁/d`, moving normaliser, recomputed baseline). Figures C-F1 `paperC_price_boundary.pdf` and C-F2 `paperC_stability.pdf` from stored data only (`FIG_paperC_endpoints.py`, 10/10); audit note `paperC_robustness.AUDIT_NOTE.md` | the odd curve strictly between `V_m(0)` and the breakpoint; `E max_k r_k`; the collapse scale (search = upper bound on the worst case only). The "still owed" entries of rows C2–C4 below are HISTORY, superseded by this row |
| **C1** prefix band, not position band | **LEAN** | `first_position_lower`, `last_position_lower` (`LeanPaperCBandV1`) — the second uses the band's **upper** side at `k=m−1` | — |
| **C1** `big` is a sum, not an exclusive choice | **LEAN** | `hband_even_of_endpoint_band` — additive expectation, no disjointness; `big` does reach `2` | — |
| **C1** objective is convex, not affine | **manuscript** | — | one wording fix in `paper_c.tex` |
| **C2** `V_m(0)` exact, both parities | **even side's VALUE now LEAN** | `flatEven_excess`/`flatEven_total` (`LeanPaperCEvenV1`) and `evenMixture_value_at_D` (`LeanPaperCMixV1`): the uniform mixture of the `m−1` insertion rankings with the flat one has per-budget value **`4/(m(m+4))`** at every budget, constant in the budget | the **feasibility**: the sign flip at `1/2`, uniform relabelling, and the per-item retained marginals (via the existing `marginal_eq_occupancy_div_card`, `relabelledLaw_invariant` — not to be re-proved); and the odd family's VALUE is now supported at **every** budget (`win_abs_sum_odd`/`win_abs_sum_even`, `LeanPaperCWindowV1`): `Σ_a|W(a,k)| = m+4` at odd budgets and `k+4` at even ones; subtracting the parity baseline `b_k = k mod 2` gives `4/m` and `(k+4)/m`, maximum `(m+3)/m` at `k=m−1` — the recorded value, confirmed rather than changed. Its marginals remain exact (`LeanPaperCCyclicV1`, deviation zero). The value itself is now Lean too (`winValue_odd/even/le/at_last`, `LeanPaperCValueV1`), and `baseline_le_abs_prefix` proves the side of `b_k = k mod 2` an upper bound needs. The base sequence is also now proved a **rearrangement of `g_m`** (`countVal_agree`, `LeanPaperCRearrangeV1`), which nothing had established — so the rotations really are a law over rankings of the family. Still owed: attainability of the baseline, and the even mixture's feasibility |
| **C3** breakpoint two-sided, every `m` | **LEAN-COND, two bridges closed** | `breakpoint_lower_odd/even`, `O2_strict_odd/even`, `O2_odd_from_prefix_band`, `O2_even_from_endpoint_band`; and now `isEvenFamily_comp` + `big_eq_sum_endpoints` + `hid_at_permutation_law` (`LeanPaperCInstantiationV1`) carry the identity to a law over **actual permutations** | `\|heavySet\| = 2` at `g_m` is **now LEAN** (`LeanPaperCFamilyV1`), together with the concrete `g_m`, its total and both parity predicates — and `isEvenFamily_not_forcing_two_heavy` shows it could not have been a corollary of the predicates. Still owed: endpoint probabilities from the prefix band at a ranking law; actual regret = normalised excess; two endpoint expectations → `max_k E r_k`; infimum over feasible laws |
| **C4** ranking ⇄ flow | **both directions now** | flow → ranking closed (`exists_rank_section`, `pathDecomposition_count_states`, no `hsec`); ranking → flow in `LeanPaperCFlowV1`: conservation is marginalisation of one joint law (`sum_joint_right/left`), plus `joint_nonneg`, `sum_occ` and **`expectation_via_occ`** — the objective transports, so it is the same optimisation and not a relaxation | **the naming step is done** (`LeanPaperCNamingV1`): the observables are `rankLayer ty k`, and conservation, non-negativity, the unit total, the objective and the **whole budget vector** all transport. Still owed: per-item band constraints, which need the relabelling route since the composition records types and not identities |
| **C5** robustness, scoped | **LEAN + manuscript** | `price_ratio_robust` (`LeanPaperCBreakpointV1`); manuscript now separates "collapse found" from "none found" | — |

---

## Methodology repairs applied to the evidence (second round)

| Repair | What it changed |
|---|---|
| `find_N`: pilot + independent confirmation, worst-world Clopper–Pearson upper bound | `r=2, h=0.4` decision budget `94 → 170`; unconfirmed candidates counted, not reported |
| error reported **per world**, worst as headline | a pooled average over a uniform prior on the truth is not a worst-case guarantee |
| every moment cell carries reps **and** a binomial upper bound | 68 cells, 7 at 16 reps; worst upper bound `0.910` — `0/16` is not near-zero |
| separation figure caption names its family | `Γ_proxy = 1/512` (r-pair family) vs `Γ_frozen = 9/512` (centred); not relabelled |
| Hellinger: stable squared-difference form; canonical **tail** seed | `r=3` fitted order `8.13 → 5.80` against the claimed `6` |
| A abstract: the frozen proxy pins extremum **indices** and drops ordering constraints | it does not forbid other cells to move |
| slope analysis relabelled a **heuristic diagnostic** | differencing removes the penalty, not the overshoot `O_α` or the residual `R_τ` |

---

## The finishing pass, after the mathematics

Not started; do **not** start it before the table above stops moving.

1. Three to four headline theorems per paper, each with model, quantifiers, parameter range,
   observation access, conclusion. Delete headlines with no theorem.
2. A table theorem → Lean declaration → construction/algorithm → figure, checking for each
   surviving hypothesis whether it is a model condition or the conclusion in disguise.
3. Audit the algorithms through the existing results: solver certificates, objective scaling,
   zero weights, oracle information, censoring, filtered failures, real query counts.
4. New experiments only where a claim lacks evidence *of the right kind*. A needs
   actual-policy behaviour, B needs a real decoder's sample error, C mostly needs nothing.
   More seeds do not fix a model mismatch.
5. Figures from locked JSON, labelled: theorem curve / certified bound / numerical
   optimisation / Monte Carlo.
6. Rewrite the manuscripts from the final results. No "was open, then half-closed" history —
   the ledger keeps that, the manuscript must read as one consistent document.
7. Novelty compared theorem by theorem, not keyword by keyword: same problem as whom, which
   assumption differs, which of our theorems does not follow from theirs. "Formalised in
   Lean" is not scientific novelty.
8. One independent adversarial read: boundary counterexamples, does the benchmark have the
   same information, every numerator and denominator of every ratio, and whether the abstract
   claims more than the theorems.
