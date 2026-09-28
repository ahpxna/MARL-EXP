# B/C progress and result audit — late snapshot, 2026-09-26

Read-only audit of the selected recent chains and their relevant manuscripts/results. No experiment or Lean build was rerun. This is not a new clean bill of health for every historical module. The user then steered the work into trained-model experiments for C; the companion research plan is PAPER_C_TRAINED_TRAFFIC_EXPERIMENT_PLAN_20260926.md.

## B: substantial completion, and two different meanings of “done”

Current source hashes match successful frozen gate records for:

- LeanPaperBParityWorldV1: smokeB1_20260926, 12 audited statements. SHA256 ca04ee0f5f2e01ef92fd6f00fc5cfe69da20b81cd1c590e089098a6c32c90dad.
- LeanPaperBDecisionMomentV1: smokeB2_20260926, 7 audited statements. SHA256 26c93de713157b9ca52c7fc4f02e2f7c697adab53efe890085a11930ff3f6d5f.
- LeanPaperBAssemblyV1: smokeB2_20260926, 9 audited statements. SHA256 bc9c635e442c998cd88067d73a85648642ec97d385f86d5c9b3a37896913df9b.

The B2 gate finished 21:19:48 -0400: 45 modules including dependencies, no failures, 352 audited statements, standard three axioms, no sorry/native_decide. Those totals are the gate dependency closure, not 352 new claims.

What their bodies prove:

1. DecisionMoment lines 152–227 computes the second moment and its 12h gap on the actual Gaussian-noisy channel. This is more than arithmetic applied to an externally supplied moment formula.
2. Assembly `endpoint_stopped` (line 215) simultaneously states safe and identification lower/upper rates on the same parity experiment. The lower side quantifies over correct stopped policies and has an existential hard world; the upper side supplies a correct policy with an all-world bound. Hypotheses include positive known σ, 0<h≤1, finite m≥2 and δ≤δ₀(m). The exponents differ nontrivially when m≥3. `endpoint_constants_pos` proves positivity of the constants/threshold. Do not restate this as an all-world lower bound or a uniform-in-growing-m result.
3. ParityWorld identifies visibility and world-dependent order on the actual channel, with χ² information. Exact KL leading constants require their own bridge; χ²-game results are not automatically KL characteristic-time identities.
4. Assembly `order_theta`/`order_theta_parity` connects the general order conditions and actual parity channel. Generic hypotheses and finite-query scope must remain visible.

## B: recent files written but not yet closed by observed gate evidence

No current-hash match was found among inspected frozen gate MODULES.tsv receipts for:

- LeanPaperBChiIntegrableV1 (143 lines, SHA e396b089b95cada8e29515bcb6266f79b06db774ff9d2ae2691dee6347d613a2).
- LeanPaperBTailMomentV1 (278 lines, SHA 52bef1ce2486d9ae28f7a50d7479b9a2cff36a5cb1cd986f1d2a9a1c0fd6cc94).
- LeanPaperBParityCriticalV1 (665 lines, SHA 8e92c5f5dc146ee3d55bc0313179d1d6cbd07cc2c3ba4f2024e69ea29b0e3db2).

ChiIntegrable supplies actual integrability of the χ² ratio/envelope. This addresses the important distinction between an integrable nonnegative statistic and Lean's totalized real integral, which is zero outside integrability. Its existence is not evidence that every earlier protocol result is invalid; the older ENNReal/lintegral chain has a separate scope.

TailMoment integrates over the head and Gaussian noise, beyond the older fixed-head finite-cube identity. ParityCritical contains Taylor expansion, χ² and KL density-integral limits, and positivity of c_j. These are source-level progress until a matching build/axiom receipt is available.

**Concrete mismatch:** the ParityCritical header promises `kappa_eq_channel` and `parity_critical_game`. Neither declaration occurs in its current body, which ends at `cj_pos`. The remaining work is not another Taylor proof: connect its density integral to the actual channel KL, instantiate the finite critical-game expansion hypotheses, then prove the claimed rescaled optimized-game limit. Also do not infer a formal Hellinger leading-constant theorem merely from the presence of KL and χ² limits.

**Manuscript stale in the opposite direction:** paper_b.tex lines 580–588 still labels the decision second moment as a by-hand certificate/arithmetic-only statement. The current gated DecisionMoment file discharges the actual-law statement. Update its evidence note and theorem references. The newer tail/critical notes should be updated only after the corresponding source is checked and the missing critical-game join exists.

## B: experiments traced back to implementation

Read the parity-constant quadrature producer, decoder/fallback producer, formal decoder figure producer and their associated saved results. The saved producer hashes match the inspected scripts for the parity-constant and corrected-decoder artifacts.

- EXP_paperB_parity_constants.py now exists. “The promised quadrature script is missing” is obsolete. It numerically evaluates the actual parity mixture and leading constants for its saved finite grid. This is not a certified integral: no independent tail-truncation, mesh-refinement and precision study was saved in the inspected artifact. High-order small-h density subtraction also merits a cancellation check before reporting extra digits. No counterexample to the saved numerical values was found in this read-through.
- EXP_paperB_decoder_leanfallback.py uses the corrected fallback, two-sided CP allocation and actual observation-only decoders. The saved 616 rows contain 11 certified budget endpoints and five identification-censored cells. A budget with a CP upper certificate is an achievable upper bound for that decoder; it is not a lower bound on optimal sample complexity.
- The lower bracket must be justified by CP lower bounds on genuinely failing budgets, not by a missing upper certificate. The inspected implementation tracks the failing prefix of the tested grid. Finite-grid slopes and upper-certificate ratios must retain those labels.
- The identification budget sums all queried schedules, whereas safe uses its decision query. Same-query-count comparisons must use total observations and not silently compare a per-query schedule length against a total.

Next focused numerical work, if desired: convergence/precision diagnostics for the critical-constant table. This audit did not rerun the decoder or quadrature grids.

## C: main text is more complete; new odd exchange module is not its headline yet

The checked CTwoMag2222Frontier source matches smokeC4_20260926 (17 audited statements; gate 52 modules/486 statements, no failures). The main manuscript now contains the all-band budget-aware formulas, even one-exchange construction, count/transport reduction and carefully labels odd one-exchange results beyond the proved ranges as numerical.

New LeanPaperCBudgetExchangeOddV1 (725 lines, SHA 59dd7163fcc0b5882c3919eed0cdc2b930eb3cf0e0702ee6b72338bebfb7a67d) has no matching receipt in the inspected frozen gates. Its body constructs the committed ranking law, proves its zero-band marginals, builds the exchange set and proves its cardinality, exchange distance and zero middle-budget cost.

**Concrete mismatch:** its header announces `recourse_one_odd` and cites `oddT_band`; the body ends after `oddT_cost`. The final marginal bound and assembled common-law recourse theorem are still absent. In particular, the band must be bounded by η/m, not merely η; the prose currently suppresses this normalization. The header is a blueprint, not a completed theorem. The m=3 case needs a separate endpoint argument if the eventual headline is all odd m≥3.

Do not upgrade the main paper's current numerical label based only on that docstring. Conversely, do not redo the already proved odd-window or even-recourse constructions.

## C: result-to-algorithm audit relevant to recourse

Read the core of EXP_paperC_budget_recourse.py and the saved paperC_budget_recourse.json. The producer hash matches. The LP uses one common initial flow and per-layer transports, preserves cardinality, enforces the radius through half the count L1 distance, and constrains both initial and final bands. Solver failure raises an error. No concrete algorithmic contradiction was found in the inspected LP construction.

Limits of the evidence:

- These are floating-point LP values, not rational dual certificates.
- The artifact records its producer hash but not the imported typed-frontier helper's hash; a full provenance bundle should record or recover that dependency version too. This is a provenance gap, not proof the results used the wrong helper.
- Some producer comments still predate the formal item-level lift. Correcting those comments should preserve the historical artifact/source linkage.
- Existing C experiments concern mathematical weight families, not trained traffic models. They cannot be relabelled as neural pruning performance.

## Immediate completion list from this snapshot

B: preserve the gated endpoint; finish actual-channel KL → critical-game assembly; gate the integrability/tail/critical additions; align manuscript evidence notes; numerically validate quadrature precision if those constants are emphasized.

C: finish the odd final-marginal and coupling join if claiming the stronger one-exchange result; gate it; retain current scope until then. A practical neural extension is a new empirical work package, detailed in the companion plan, not something the existing proof or toy LP data already establish.
