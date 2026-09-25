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

## State on 2026-09-25 — supersedes the 2026-09-24 section where they conflict

Full gate `full6_20260925` PASS: 214 modules, 1666 audited theorems, standard axioms, no drift,
`report/MODULES.tsv` sha256 `6e1106bd7773b2fe…`. It builds every module named below.

| # | Status | Headline, on the paper's own object | Final theorem (module) | Hypotheses left | Scope that must travel with it |
|---|---|---|---|---|---|
| A-SAC | **headline** | Every δ-correct policy must give up a BUDGET of surrogate value: `N·sacrifice(w̄) ≥ 8rM·D`, `D = (1−δ)log(1/δ) − log 2`, with `sacrifice(w) = 1 − (512/9)J_fr(w)`; the ideal learner meets it, `1/Γ ≤ 128(4+2rM)/9` | `sacrifice_cost_law`, `pair_demand`, `middle_demand`, `middle_le_sacrifice`, `exchange_strict`, `strict_frontier`, `upper_constant`, `constant_gap` (`LeanPaperASacrificeV1`); `ideal_sacrifice`, `sacrifice_hypotheses_satisfiable` (`LeanPaperASacrificeIdealV1`) | `M>0`, `r>0`, `0<δ<1` | a budget in query-units, not a fraction; the two constants differ by `32/9 + 64/(9rM)`. A small sacrifice over a long run (dilution) is NOT proved |
| A-DIL | **headline** | The budget can be spread over any run length: padding a δ-correct π0 with 4k round-robin surrogate-optimal queries keeps it δ-correct, gives `N = N0 + 4k`, `8rMD ≤ N·sac(w̄) ≤ N0·sac(w̄0)`, and `sac(w̄) ≤ N0/(N0+4k)` | `sacrifice_mix_le`, `padPol`, `pad_real`, `lintegral_cnt_pad`, `padCnt_A`, `dilution`, `dilution_small` (`LeanPaperASacrificeDiluteV1`) | those of `sacrifice_cost_law` for π0 (satisfiable: `sacrifice_hypotheses_satisfiable`) | padding happens AFTER the decision; lowering the budget itself below N0 is not proved |
| A-FORCE | **law** | Any forcing schedule with `Mid ≤ c T^a + B` pays `E T ≥ ((8rMD − b)/c)^{1/a}` | `forcing_law`, `power_forcing_law` (`LeanPaperASacrificeV1`) | the pathwise middle-count hypothesis | a property of the learner; A6″ proves its own |
| A-S | **audit** | The surrogate re-solved at an estimate is not the centred surrogate: equal `9/512` at the truth, `9/512` vs `≥ 9/512 + u²/4` under a common shift | `frozenGameAt_thetaC`, `frozenAt_unif_shift`, `centred_unif_shift_ge`, `two_surrogates_differ` (`LeanPaperA6TwoSurrogatesV1`) | — | A-H5″ is about the UNRESTRICTED surrogate |
| A-F2d | **NUM, locked, paired** | 200 paired runs per cell, `r ∈ {1,2,4}`, `M ∈ {1,4}`, both worlds: 0 wrong among 6258 stopped of 7200 launched; base world surrogate-at-estimate certifies 167/41/44/2/4/0 of 200 (others 200/200) with paired excess 1.9–5.4·10⁴ rounds over geometry; swapped world the surrogate rule is fastest in every cell | `paperA_deployable_paired.pdf` (`EXP_paperA_deployable_paired.py` 5/5 incl. transcribed `oCount_le_bad`; `FIG_paperA_deployable_paired.py` 7/7) | — | restricted mean (censored runs count B, so surrogate excess is a lower bound); α ≫ δ₀; lower certificate, not `tauG`. Resolves deviation P-2 (`paperA_deployable_paired.PROVENANCE_NOTE.md`) |
| B-LAW | **headline** | Minimax safe-decision cost from obstructions: every finite-horizon policy has `cost(w₀)·t* ≥ ((1−δ)/(|W|−1))log(1/δ) − log 2`; a tournament attains `O(|W|² log(|W|/δ)/t*)`; on graded channels `t* = C h^{2s*}` | `obstruction_value`, `obstruction_lower`, `obstruction_lower_star`, `tournament_law`, `graded_resolves_iff`, `graded_tStar` (`LeanPaperBObstructionLawV1`); `obstruction_lower_chi`, `parity_graded`, `parity_safe_from_law`, `parity_id_from_law`, `tournament_satisfiable` (`LeanPaperBObstructionParityV1`) | upper side: pairwise tests of exponent `cκ` | lower unconditional on every channel in protocol form; upper conditional |
| B-LAW′ | **headline** | The same lower law for EVERY policy that stops almost surely, at level `2δ` | `stopped_obstruction_lower`, `stopped_obstruction_lower_chi`, `stopped_obstruction_lower_star`, `trunc_correct`, `outT_first`, `costSt_ofFinite`, `correctSt_ofFinite` (`LeanPaperBStoppedLawV1`) | `0<δ`, `2δ≤1` | a.s. stopping uniform over the finite world set; cost = `sup_n` of truncated costs. Supersedes B-H5′'s parity-only scope |
| B-FAM | **headline** | Both minimax rates on the latent Gaussian family, over every finite family of unit-`ℓ₁` linear probes: `Θ(log(1/δ)/h²)` safe, `Θ(log(1/δ)/h^{2r})` identification, lower over every a.s.-stopping policy | `famChan`, `famDens_vdiff`, `famDens_udiff`, `famChi_v_le`, `famChi_u_le`, `family_safe_lower`, `family_id_lower` (`LeanPaperBFamilyChannelV1`); `charFun_famLaw`, `decMean_eq`, `dec_gap_lower`, `tailMean_eq`, `tail_gap_lower` (`LeanPaperBFamilyLawV1`); `near_error`, `safe_decoder_error`, `id_decoder_error`, `family_safe_rate`, `family_id_rate`, `family_safe_minimax`, `family_id_minimax` (`LeanPaperBFamilyDecoderV1`); `family_safe_stopped_rate`, `family_id_stopped_rate` (`LeanPaperBStoppedLawV1`) | `r>0`, `σ>0`, `0<h≤1`, `0<δ≤1` | `famSafe` is STATED as the correspondence `EXP_paperB_construction` computes (checked 2026-09-25); constants depend on `r` and `σ`. Supersedes B-H5/B-H5′'s "F_{u,v} adaptive instantiation still open" and `LeanPaperBHeadlineV1`'s Chebyshev side |
| B-HEL | **headline** | The upper law on EVERY channel: block likelihood-ratio tests err with probability `≤ BC^n ≤ e^{−n κ_H}`; the tournament is safe w.p. `≥ 1−δ` within `|W|² ⌈log(|W|/δ)/t*_H⌉` queries; `κ ≤ Kκ_H ⇒ t* ≤ K t*_H` | `bc_le_one`, `lintegral_sqrt_ratio`, `lintegral_prod_sched`, `block_error`, `bc_pow_le`, `beatH_anti`, `beatH_error`, `hellinger_tournament`, `hellinger_upper_star`, `resolved_le_scale`, `gChan_bc`, `hellinger_tournament_satisfiable` (`LeanPaperBHellingerTestV1`) | `t > 0` with `Resolves κ_H safe t` (satisfiable: Gaussian ±1 channel, `t = 1 − e^{−1/2}`) | finitely many queries; scheduled (non-adaptive) tournament; matches the lower law only where KL and Hellinger informations are comparable. Supersedes B-LAW's "upper conditional on a test hypothesis" |
| B-TIGHT | **headline** | The general law is tight on both channels: a feature gap forces Hellinger information (`(∫|p−q|)² ≤ 8H²`), so the general Hellinger tournament attains the latent family's `Θ(log(1/δ)/h²)`, `Θ(log(1/δ)/h^{2r})` and the parity channel's `Θ(log(1/δ)/h²)`, `Θ(log(1/δ)/h^{2(m−1)})`; with the lower law all four rates are corollaries of the one law | `tvs_sq_le`, `feature_gap_le`, `gap_sq_le_hel`, `fam_hel_u`, `fam_hel_v`, `fam_resolves_safe`, `fam_resolves_id`, `family_safe_general_upper`, `family_id_general_upper` (`LeanPaperBHellingerFamilyV1`); `Gc_anti`, `parity_hel_sep`, `parity_kH_graded`, `parity_resolves_safe`, `parity_resolves_id`, `parity_safe_general_upper`, `parity_id_general_upper` (`LeanPaperBHellingerParityV1`) | family: `r>0`, `σ>0`, `0<h≤1`; parity: `m≥2`, `σ>0`, `0<h<1` | scheduled tournament; constants explicit, not uniform in `r`, `m` |
| B-SAFE | **completes B-FAM** | The latent family's safe sets are DERIVED from its losses: `E[F|z_j=b] = c_j b`, losses `|3u−4−c_j|`, near-minimisers = `famSafe`, independent of `v` | `sum_zero_of_flip`, `resp_eq`, `loss_eq`, `famSafe_derived` (`LeanPaperBFamilySafeV1`) | `r ≥ 2`, `0 ≤ ε < 1` | supersedes "famSafe is stated" |
| A-STOP | **completes A-SAC** | The sacrifice law for every policy that stops almost surely at θ_C (level 2δ, finite expected counts) | `outT_unfired`, `trunc_A`, `expCntSt`, `sacrifice_law_stopped`, `correctA_ofFinite` (`LeanPaperASacrificeStoppedV1`) | a.s. stopping at θ_C only | the forcing law stays finite-horizon |
| A-BOTH | **headline (re-cited)** | Both mispricing directions after the sup over designs on the 8-cell compression class: `≤ 64/M` and `≥ M/96`; no constant factor | `low_separation_at_world`, `high_separation_at_world`, `exists_low_games`, `exists_high_games`, `no_constant_factor_on_families` (`LeanPaperASeparationV1`) | `M > 0` | closes A1 (was mis-tracked as open); fixed-design 3-cell families now exact (`EXP_paperA_frozen_proxy_exact`, 7/7, CERT) |
| C-ODD | **headline** | `V_m(η) = max{(m+3−(m+1)η)/m(m+4), V_free + max(0,1−η)/m(m+4)}` for every odd `m≥3`, `η≥0`; kink at `η_t = 1−2/m(m−1)` | `odd_frontier`, `odd_kink_value`, `kink_law` (`LeanPaperCOddFrontierV1`); `relaxed_value_odd` (`LeanPaperCRelaxedJoinV1`); `odd_line2_value` (`LeanPaperCOddKinkV1`) | — | — |
| C-COLL | **headline** | The worst-case PRICE ratio under weight perturbation is `Θ(min(m, 1/ε))` | `collapse_upper`, `collapse_lower` (`LeanPaperCCollapseScaleV1`); `physical_price_linear` (`LeanPaperCRatioJoinV1`) | `ε ∈ [1/m, 1/6]` for the lower side | supersedes C-H4's "the price's collapse point is not located" |
| C-WIN | **completes C-COLL** | Every perturbation with `ε ≤ 1/m` and positive perturbed value keeps price ratio `≥ (m−1)/8`; hence `≥ min(m−1, 1/ε)/16` on all of `0 < ε ≤ 1/6` | `window_arith`, `collapse_window`, `collapse_all`, `collapse_window_satisfiable` (`LeanPaperCCollapseWindowV1`) | positive perturbed free value | closes the window `(1/2m, 1/m)` left by `collapse_lower` |
| C-EXPOST-BAND | **headline** | `V^post_m(η) = 2/(m+4)` (even `m≥4`), `(2 + 2max(0,1−η)/m)/(m+4)` (odd `m≥3`) | `expost_even`, `expost_odd` (`LeanPaperCExPostBandV1`) | — | ex post the band costs at most a factor `1 + 1/m` |

## State on 2026-09-24 — supersedes the status column of the tables below where they conflict

The rows further down are kept as the record of how each claim was reached, including their
retractions. Where a row below says "open", "owed" or "conditional" and a row here names a
final theorem, this row is current. Gate: smoke `smokeA_20260924_ideal` PASS (54 modules;
the closure of `LeanPaperA7IdealFamilyV1`); full gate `full3_20260924_ideal` PASS
(188 modules, 1505 audited theorems, standard axioms; proof hashes in its `report/MODULES.tsv`).
Latest full gate: `full4_20260924` PASS (196 modules, 1547 audited theorems, standard axioms, no drift; covers every A6, A6″ and B-2 module; `report/MODULES.tsv` sha256 `e9c5683109be38fc…`).
The A-H5′ modules postdate that freeze: smoke gate `smokeA6_20260924` PASS (57 modules, 447 theorems, standard axioms; `report/MODULES.tsv` sha256 `abcc1614b0869841…`).

| # | Status | Headline, on the paper's own object | Final theorem (module) | Hypotheses left | Scope that must travel with it |
|---|---|---|---|---|---|
| A-H4′ | **headline, for the IDEAL learner** | The defined learner attains the exact rate: `E τ_δ / log(1/δ) → 1/Γ_actual`, `E τ_δ < ∞` at every `δ`; wrong answer w.p. `≤ δ` | `ideal_family_finish`, `ideal_family_correct`, `GamT_fam` (`LeanPaperA7IdealFamilyV1`); `ideal_upper_rate`, `ideal_finite`, `ideal_correct` (`LeanPaperA7IdealUpperV1`); `ideal_direct` (`LeanPaperA7IdealDirect2V1`); lower via `runS_eq`, `cnt_le_tau`, `ansEv_alt_le`, `ansEv_true_ge` (`LeanPaperA7IdealStoppedV1`) + `stream_eq_hist_fresh` + `family_policy_lower` | `M>0`, `r>0`, `a>0` only | IDEAL: exact `J` over a refining net, exact GLR infimum (`ν_t = 0`). NOT `EXP_paperA7_learner.py`; the shipped learner stays under A-H4 (conditional). Rate and finiteness at `θ_C`; correctness at every world with one correct answer. No numerical artifact comes from this learner |
| A-H5′ | **headline, ORACLE-ALLOCATION** | Tracking any exact optimum of the frozen surrogate costs `E τ_δ ≥ (KM/8)² log²(1/δ)` (`K = 4+2r`), against `O(log(1/δ))` for the ideal learner; the ratio is unbounded | `surrogate_optimum_cost`, `surrogate_vs_ideal`, `starved_cost_log_sq`, `starved_lower_at`, `klq_pair`, `surrogate_optimum_exists`, `uniform_surrogate_cost` (`LeanPaperA6SurrogateCostV1`); `fCount_le_amgm` (`LeanPaperA6FixedDesignV1`); `cnt_eq_at_min`, `ansEv_alt_leG`, `ansEv_true_geG` (`LeanPaperA7StoppedGenV1`) | `M>0`, `a>0`, `r>0`; `w⋆` an allocation with `frozenValueC₀ M w⋆ = frozenGameC₀ r M` (satisfiable: `surrogate_optimum_exists`) | the tracked design is the surrogate optimum AT THE TRUE WORLD, held fixed (true extrema enter the allocation). Supersedes A-H5's two remaining inputs FOR THIS LEARNER ONLY; a learner recomputing the surrogate at its estimate is not covered. Stop = true-alternative GLR. No numerical artifact |
| A-H5″ | **headline, DEPLOYABLE learner** | The learner that RE-SOLVES the frozen surrogate at its own estimate every round (or uses any oracle returning an exact surrogate optimum at estimates with anchor extrema), with forcing `1/√(s+1)` and the true GLR stop, has `E τ_δ ≥ (KM/8)² log²(1/δ)` for `δ < δ₀`; ratio to the ideal learner unbounded | `est_cost_log_sq`, `surrogate_learner_cost`, `exact_oracle_cost`, `surrogate_learner_vs_ideal`, `est_lower_at` (`LeanPaperA6EstCostV1`); `frozenGameAt_eq`, `starvation_at`, `surD_exact`, `optimal_oracle_middle_zero` (`LeanPaperA6SurrogateAtV1`); `radius_eventually`, `close_of_good`, `badAll_expect` (`LeanPaperA6BadRoundsV1`); `oCount_le_amgm`, `oCount_ge` (`LeanPaperA6OracleLearnerV1`) | `M>0`, `a>0`, `r>0` | the oracle sees only the estimate (no true-world information); misleading rounds cost `≤ s₀+2` in expectation (Ville at the learner's own statistic). `δ₀` explicit but tiny. Supersedes A-H5′'s oracle-allocation restriction |
| A-F | **NUM + theorem** | Centred separation interval and allocation mechanism | `paperA_mechanism.pdf` (`FIG_paperA_mechanism.py`, 7/7) | — | the runs certify answer A only: allocation diagnostic under one certificate, not a learner (`paperA_mechanism.PROVENANCE_NOTE.md`, addendum) |
| A-F2b | **NUM + theorem check** | Certificate rate and `E[min(τ,b)]` by budget; middle share along one run | `paperA_budget.pdf` (`FIG_paperA_budget.py`, 5/5, incl. the transcribed `fCount_le_quota` bound on the proxy trace) | — | same stored runs as A-F (no resampling). The proxy rule is `fixLearner (wUnifC r)` up to a forcing offset, an ORACLE ALLOCATION. Its stop is the A-only certificate, and α = 0.05 lies outside `δ₀` of `uniform_surrogate_cost`: direction-consistent, not a test (`paperA_mechanism.PROVENANCE_NOTE.md`, addendum 2) |
| A-F2c | **NUM, deployable policies** | Under ONE two-answer certificate (no true label in the stop), the learner that re-solves the surrogate at its estimate certifies in 22/3/0/0 of 24 runs at r = 1/2/4/8 on the base world, while the true-game and uniform learners certify every run; 0 wrong among 505 stopped runs | `paperA_deployable.pdf` (`EXP_paperA_deployable.py` 6/6 incl. the transcribed `oCount_le_bad`; `FIG_paperA_deployable.py` 4/4) | — | α = 0.05 ≫ δ₀; certificate is a lower bound, not `tauG`'s infimum: behaviour of these rules, not a test of `Ω(log²)` (`paperA_deployable.PROVENANCE_NOTE.md`). Resolves deviation P-1 |
| A-F1 | **NUM, certified (exact rational)** | `Γ_true/Γ_proxy ∈ [0.8372,0.8374], [0.7214,0.7216], [0.5664,0.5667], [0.3982,0.3982]` at r = 1, 2, 4, 8 (M = 1), with centring and every region | `paperA_certified.pdf` (`EXP_paperA_certified_separation.py` 6/6: cover = Alt, exact alternatives, regional duals, theorem consistency; `FIG_paperA_certified.py` 3/3) | — | numbers at four r; the all-r statement is `centred_separation`. Γ_proxy = 9/512 is the theorem. Resolves deviation A-6 |
| B-H5 | **headline, on the parity channel** | Both minimax rates on ONE channel: `Θ(log(1/δ)/h²)` safe, `Θ(log(1/δ)/h^{2(m−1)})` identification, uniform on a rectangle | `parity_tip_finish`, `parity_rates`, `safeCert`, `idCert` (`LeanPaperBParityFinishV1`); `safeLower`, `idLower` (`LeanPaperBParityExperimentV1`); `transcript_kl_le` (`LeanPaperBProtocolV1`) | `m≥3`, `σ>0` | randomised adaptive policies with a FINITE horizon (bounded stopping). Supersedes B-H3's "continuous alphabet open" and B-H4's "upper side in δ" for this channel; the `F_{u,v}` family's adaptive Gaussian instantiation is still open |
| B-H5′ | **headline, unbounded stopping** | The same two rates over EVERY randomised adaptive policy that stops almost surely (no bound on τ, E τ possibly infinite): lower at level 2δ, upper by the decoders embedded as stopping policies | `stopped_parity_rates`, `stopped_lower_log`, `stopped_safe_lower`, `stopped_id_lower`, `trunc_correct`, `outT_first`, `ofPol_correctS`, `costS_ofPol`, `hist_map_restr` (`LeanPaperBStoppedParityV1`, smoke gate `smokeB2_20260924` PASS) | `m≥2`, `σ>0`, `0<h≤1`, `2δ ≤ min(δS, δI)` | cost = sup over horizons of E[non-dummy queries] (= E τ by monotone convergence). A.s. stopping is required uniformly over the m worlds (one horizon per ε). Closes deviation B-2 FOR THIS CHANNEL; the `F_{u,v}` family's adaptive Gaussian instantiation is still open |
| B-D | **provenance** | Decoder counts vs the formalized decoder | `lean_wrong_imp_py_wrong` (`LeanPaperBDecoderMatchV1`) | — | identification counts are a CONSERVATIVE UPPER bound on the formalized decoder's error, not a measurement of it (`paperB_decoder.PROVENANCE_NOTE.md`) |
| B-D′ | **paired rerun** | The certified identification budgets are the FORMALIZED decoder's own | `lean_wrong_imp_py_wrong` checked on data: `paperB_decoder_leanfallback.json` (`EXP_paperB_decoder_leanfallback.py`, 10/10; same draws: all 308 safe counts equal, every identification count ≤ the script's, 13,831 errors removed) | — | at the corrected family-wise level no certified budget moves; drawn lower brackets remain the script rule's (conservative). Supersedes B-D's 'not a measurement of it' for the upper budgets |
| C-H1′ | **headline** | `V_m(0)` exact: `4/m(m+4)` even, `(m+3)/m(m+4)` odd | `even_value_zero`, `odd_value_zero` (`LeanPaperCEndgameV1`); the laws `even_endpoint_law`, `odd_endpoint_law` (`LeanPaperCEndpointLawV1`) | — | supersedes C-H1's "one construction owed" |
| C-H2′ | **headline** | Even: the whole frontier `V_m(η) = max{2/(m+4)(m−1), 4(1−η)/m(m+4)}`; odd: `V_m(η) = V_free ⇔ η ≥ 1` | `even_frontier_all`, `odd_breakpoint`, `oddBreakpointFinish_holds` (`LeanPaperCEndpointLawV1`) | — | the odd curve strictly between its anchors is not claimed |
| C-H3′ | **headline** | The ranking program and the four-type flow program have the SAME value, all bands carried | `actual_banded_infima` (`LeanPaperCFlowBandJoinV1`); `value_eq_flow`, `even_frontier_flow`, `odd_breakpoint_flow` (`LeanPaperCFlowObjectiveV1`) | — | a statement about the VALUE on `g_m`, not an algorithm for perturbed weights. Supersedes C-H3's "nothing in the gated corpus proves it" |
| C-H4′ | **headline** | The physical optimum is the paper's value, and moves at most `3‖g−g'‖₁/d` | `familyBaselineIdentification_holds` (`LeanPaperCBaselineAttainV1`); `trueValue_family`, `family_value_robust`, `even_frontier_robust` (`LeanPaperCStabilityFamilyV1`); `trueValue_stable` (`LeanPaperCStabilityEndgameV1`) | `0 < d ≤ min(‖g_m‖₁, ‖g'‖₁)` | moving normaliser, recomputed baseline, per-item bands, feasible set fixed. An envelope; the collapse scale is a separate result (C-H4) |
| C-H5′ | **headline (free case)** | Choosing the budget AFTER the draw: `inf_P E_P[max_k r_k] = 2/(m+4)` at every `m ≥ 3`, exactly `m − 1` times the ex-ante `V_free`; ex-ante ≤ ex-post for every law | `pathValue_eq`, `path_over_free`, `exists_defect`, `worstBudget_even`, `worstBudget_odd`, `objective_le_pathObjective` (`LeanPaperCExPostV1`, post-full4; smoke `smokeCEP_20260924` PASS) | `m ≥ 3` | FREE case only; the banded ex-post problem is not solved; the band factor and the timing factor are NOT multiplied. Joins C's own `regret`/`gFamily`, not the Structural lists. Resolves deviation P-4 |
| C-F | **NUM + theorem** | C-F1 price/phase boundary, C-F2 stability | `paperC_price_boundary.pdf`, `paperC_stability.pdf` (`FIG_paperC_endpoints.py`, 10/10) | — | all 220 stored perturbations under the Lean envelope (worst 0.32); the robustness check name "floor is LOOSE" over-claims (`paperC_robustness.AUDIT_NOTE.md`) |


### Proof hashes (gate `full3_20260924_ideal`, VERIFY PASS)

sha256 of the frozen source and of the built `.olean`, first 16 hex digits; full digests in
`work/gate_runs/full3_20260924_ideal/report/MODULES.tsv`. Every row: exit 0, no `sorryAx`.
`LeanPaperCCollapseV1` drifted after the freeze (docstring only).

| headline | module | source sha256 | olean sha256 |
|---|---|---|---|
| A-H4′ | `LeanPaperA7IdealFamilyV1` | `3fbfcaf2442b4c65` | `d294a0ea0c638ba6` |
| A-H4′ | `LeanPaperA7IdealUpperV1` | `9b6509cc25a8a48e` | `ef016e840de64e88` |
| A-H4′ | `LeanPaperA7IdealDirect2V1` | `8c3c7d862b227b33` | `c9fe1d471aefadbf` |
| A-H4′ | `LeanPaperA7IdealStoppedV1` | `985ebb0d1069e499` | `36583be2877b477b` |
| B-H5 | `LeanPaperBParityFinishV1` | `40365d730c496280` | `117343893e7c9d70` |
| B-H5 | `LeanPaperBParityExperimentV1` | `084d825980f1485b` | `5ec896a1ec18145e` |
| B-H5 | `LeanPaperBProtocolV1` | `61be5805df327c9e` | `85c59cd47b0d3ab4` |
| B-D | `LeanPaperBDecoderMatchV1` | `e894a6f4d5df265b` | `c329af1af4feb237` |
| C-H1′, C-H2′ | `LeanPaperCEndgameV1` | `5be5872c8c1cad0f` | `8e3d423d31531396` |
| C-H1′, C-H2′ | `LeanPaperCEndpointLawV1` | `6e78d930ae3f89d9` | `1dd5320f4685106f` |
| C-H3′ | `LeanPaperCFlowBandJoinV1` | `89f63f3431e672f4` | `1b63b5924d55d9d7` |
| C-H3′ | `LeanPaperCFlowObjectiveV1` | `f5abebde8617fb50` | `26bc81a4d99d2ffb` |
| C-H4′ | `LeanPaperCBaselineAttainV1` | `c3963a0ccfaf92ca` | `946c94fb13b5cef3` |
| C-H4′ | `LeanPaperCStabilityFamilyV1` | `8f75b915d14a5b7e` | `346faa4c356eef8d` |
| C-H4′ | `LeanPaperCStabilityEndgameV1` | `32de317c9e4b7c31` | `54cd079834bc1562` |
| C-H4 (floor) | `LeanPaperCCollapseV1` | `c564c0a13b53738c` | `c97488472d41df0d` |
| A-H5′ | `LeanPaperA6FixedDesignV1` (smoke `smokeA6_20260924`, PASS, 57 modules, 447 theorems) | `39f570fbf5cff62b` | `191918b946ae6ab0` |
| A-H5′ | `LeanPaperA7StoppedGenV1` (same smoke gate) | `8b49d2693f9cbe93` | `d711be37e86d47e1` |
| A-H5′ | `LeanPaperA6SurrogateCostV1` (same smoke gate) | `587866f618c84d25` | `955b1814e64b5936` |
| B-H5′ | `LeanPaperBStoppedParityV1` (smoke `smokeB2_20260924`, PASS, 34 modules, 251 theorems) | `eb59652070dd1f32` | `7fd3c25f405691a1` |
| C-H5′ | `LeanPaperCExPostV1` (smoke `smokeCEP_20260924`, PASS, 36 modules, 371 theorems) | `702753f661ea0953` | `0a2832f3e7742e83` |
| A-H5″ | `LeanPaperA6OracleLearnerV1` (smoke `smokeA6est_20260924`, PASS) | `e155422a8a373046` | `c4bd7b7b80f361a4` |
| A-H5″ | `LeanPaperA6SurrogateAtV1` (smoke `smokeA6est_20260924`, PASS) | `5906fa0c4d759f26` | `68e81f6bd3f64147` |
| A-H5″ | `LeanPaperA6BadRoundsV1` (smoke `smokeA6est_20260924`, PASS) | `fe4a98e82a4fc5fb` | `ee7f806e3b704919` |
| A-H5″ | `LeanPaperA6EstCostV1` (smoke `smokeA6est_20260924`, PASS) | `9a4e18917b6ac240` | `3f97f09b7fee585d` |

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
| C-H4 | **headline** | Robustness has an exact reach: at `ε ≤ 1/2m` the linear price survives; at fixed `ε` the same bound certifies nothing linear | `ratio_linear_at_small_eps`, `ratio_bounded_at_fixed_eps` (`LeanPaperCTransport2V1`) | weight perturbation with `D` and the feasible set held fixed | `paperC_perturbation.json`, `paperC_robustness.json` | **the FLOOR's collapse point is located, the PRICE's is not** (corrected 2026-09-24): `ratio_collapse_lower` and `ratio_bounded_at_fixed_eps` pin the floor expression `Rat(m,ε)` between `(1/8)·min(m−1, 1/ε)` and `2/ε`, so the GUARANTEE is `Θ(min(m, 1/ε))` and stops being linear at `ε_c = 1/(m−1)` (`LeanPaperCCollapseV1`). Where the true worst-case price collapses would need an upper bound on the true ratio, i.e. a proved destructive perturbation; none is proved, and the adversarial search gives only attained examples. An earlier version of this row said "the order is `min(m, 1/ε)` from both sides", which read as a statement about the price. Band relaxation at fixed `η` is a different result and is still not combined with this one |


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

---

## Upgrade round 2026-09-25 (targets v2: `PLAN_UPGRADE_ABC_20260925.md`)

| Paper | Statement (manuscript label) | Lean | Status |
|---|---|---|---|
| A | Budget classes nested; eventual class excess `(1-b)t₀/E\|N\|`; `E[s]` constraint escapes (`prop:classes`) | `LeanPaperAPolicyClassesV1`: `prefix_terminal`, `terminal_eventual`, `terminal_expected`, `eventual_expected`, `mean_escapes` | **LEAN** |
| A | Repair law (i) lower, any channel (`thm:repairlaw`) | `terminal_budget_law`, `eventual_budget_law` on `budget_law` (`LeanPaperARepairLawV1`) | **LEAN** |
| A | Repair law (ii) attainment, any eventually-informative oracle; fixed design | `LeanPaperABudgetUpperV1`: `oracle_direct`, `oracle_expect_bound`, `oracle_correct`, `fix_expect_bound`, `fix_upper_rate` | **LEAN** |
| A | Repair law (iii) realised design enters the budget, every path | `fix_design_floor`, `Jval_ge_scale`, `fix_budget_eventually` | **LEAN** |
| A | Frontier = optimal budgeted rate (`cor:repairrate`) | coupling `stoppedG`, `runSG_eq`, `cnt_eq_at_min` | **LEAN** for concavity and limit steps (`LeanPaperARepairRateV1`); the Gaussian identification of the two budget notions is a written step (stated in the paper) |
| A | No threshold, linear repair (`prop:shape`) | `no_threshold`, `linear_repair` | **LEAN** |
| A | Two arms: exact frontier and attained rate (`prop:twoarm`) | `two_arm_frontier` etc.; `LeanPaperATwoArmRateV1`: `jw_two`, `jf_two`, `two_arm_budget_rate`, `two_arm_eventually` | **LEAN** |
| B | Certificate channel: KL factor `1/(\|W\|-1)` necessary (`prop:certchannel`) | `LeanPaperBCertificateChannelV1`: `cert_tight` | **LEAN** |
| B | Decision order at a world; hardest world has order `s*` (`prop:dorder`) | `LeanPaperBDecisionOrderV1`: `decision_upper`, `decision_lower`, `max_order_iff` | **LEAN** (ultrametric hypothesis for the hardest-world identity) |
| B | Critical game: `h^{-2s}·game → G*` (`thm:critical`) | `LeanPaperBCriticalGameV1`: `critical_limit`, `expansion_hyps`, `decision_limit` | **LEAN** |
| B | Same order, constants `k` apart (`prop:sameorder`) | `private_game`, `shared_game`, `same_order_ratio` | **LEAN** |
| B | Query design as hitting set (`thm:hitting`) | `dec_hitting`, `id_implies_dec`, `dec_mono`, `gap_example` | **LEAN** |
| B | Every hitting set is a design problem (`thm:hittingembed`) | `LeanPaperBQueryDesignV1`: `hitting_embeds`, `order_zero_fails`, `order_two`, `id_iff_hitting` | **LEAN**; NP-hardness (Karp) and greedy `H_n` (Johnson, Chvátal) cited |
| C | Flow program for every typed multiset, `∏(n_τ+1)` states (`thm:typedflow`) | `LeanPaperCTypedFlowV1`: `typed_flow_equivalence`, `typed_banded_infima`; `LeanPaperCFreeBandV1`: `support_box`, `card_box` | **LEAN** |
| C | Free threshold, attained, read off the flow program (`thm:freeband`) | `attain_value`, `attain_eta`, `free_threshold`, `free_threshold_flow` | **LEAN** |
| C | Additive price stable (`prop:gap`) | `gap_nonneg`, `gap_antitone`, `gap_zero_iff`, `gap_stable` | **LEAN** |
| A | Frontier concave, continuous inside, near-optimal design strictly inside the budget, lower limit (`cor:repairrate`) | `LeanPaperARepairRateV1`: `R_concave`, `R_continuousAt`, `near_design`, `frontier_lower_rate` | **LEAN** |
| C | `(a,-a,b,-b)`: `V(η) = ((a-b)/(2(a+b)))·max((1-η)/2, 1/3)` at every ratio (`thm:twomag`) | `LeanPaperCTwoMagFourV1`: `per_order`, `lower_band`, `lower_free`, `law_feasible`, `law_obj`, `twoMag_frontier`, `twoMag_price` | **LEAN** |
| C | Two-magnitude phase map (`sec:typed`) | `scripts/EXP_paperC_typed_frontier.py` → `paperC_typed_frontier.json` (sha 2a572a64ce84, 3/3 checks) | **NUM**; region laws open |

Gates, all PASS with standard axioms, no sorry and no drift:
- `smokeUP1_20260925`: 79 modules, 762 theorems (CertificateChannel, RepairLaw, DecisionOrder,
  TypedFlow);
- `smokeUP2_20260925`: 107 modules, 934 theorems (PolicyClasses, BudgetUpper, CriticalGame,
  QueryDesign, FreeBand);
- `smokeUP3_20260925`: 106 modules, 924 theorems (TwoArmRate, RepairRate, TwoMagFour).
