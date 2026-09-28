# E1 — controlled calibration benchmark (MARL_FINAL_SCOPE §5): results, 27/09/2026

This file does not edit any ledger and has not been gated. It is a controlled simulation, not traffic
and not learned MARL.

## Provenance

- **Producer:** `scripts/MARL_E1_controlled_calibration.py`. This run's source sha is 1d16e244…
- **Result:** `research/marl_budget/e1_controlled_v2_20260927_191405/e1_results.json`, COMPLETE,
  205 s, seed 0.
- **Self-check:** the closed-form value matches Monte-Carlo rollouts of the Bayes decoder
  (max |diff| 0.023 over 6 random sets × 200k draws). The script refuses to write results if this
  fails.
- **Superseded run:** `e1_controlled_20260927_*`, kept unchanged, produced by an earlier version of
  the same script (its sha is in its JSON).
  - That version decided with a plug-in z-quantile LCB and allowed 2 samples per candidate. This was
    anti-conservative at small N and produced a harmful spike at N = 400, R = 2.
  - v2 uses a Student-t Bonferroni LCB with at least 5 samples per scored candidate. It also computes
    the geometric floor on the same instances as the curves.
  - v1 figures are archived in `legacy/figures_20260927_e1v1/`.
- **Figures:** `research/marl_budget/figures_20260927/fig2_controlled_frontier.png` and
  `fig4_acquisition_ablation.png`.

## E1a — the exact model of T2 (`LeanMarlRepairCalibrationV1`)

Setup:
- Needle class with uniform-gap gains (γ = 1, ε = 0.5, β = γR + ε + 1), so every reachable
  non-prefix repair is ambiguous.
- Unit-Gaussian excess observations.
- 4,000 trials per point. Worst case = max(null-world error, needle-world error).

| m, k, R | \|Amb\| | C(m,k) | proved lower (null-world cost) | N at α = 0.05, targeted block tests | proved upper (construction) | N at α, uniform over all k-sets | proxy only |
|---|---|---|---|---|---|---|---|
| 6, 3, 1 | 9 | 20 | 6 | 56 | 63 | 122 | never |
| 8, 4, 1 | 16 | 70 | 11 | 99 | 128 | 365 | never |
| 6, 3, 2 | 18 | 20 | 6 | 66 | 72 | 66 | never |
| 8, 4, 2 | 52 | 70 | 18 | 248 | 260 | 322 | never |
| 10, 5, 2 | 125 | 252 | 44 | 597 | 750 | 1303 | never |

Reading:
- The measured cost always lies between the two proved bounds and grows linearly with |Amb|.
- The symmetric design pays about (C(m,k) − 1)/|Amb| times more, as `symmetric_design_cost`
  predicts: predicted 4.3, 1.1, 1.3, 2.0 against measured 3.7, 1.0, 1.3, 2.2.
- A proxy that never rolls out an ambiguous repair never reaches α (`zero_allocation_impossible`).
- These numbers check the proved law on its own model. They add no new theorem.

## E1b — an executable-actor communication task

**Model.** The value is generated, not assigned.
- Senders observe x_j ∈ {−1, +1}.
- Target: Y = Σ g_j x_j + β x_a x_b + σ₀ξ, with a hidden interacting pair (a, b). One member alone is
  worthless.
- The receiver is the Bayes decoder; reward is −(Y − Ŷ)².
- Parameters: m = 10, k = 4, g² = linspace(1, 0.1), β² = 1.6, σ₀ = 0.5.
- Prefix = top-4 by first-order importance g².
- 200 instances; (a, b) is drawn uniformly over all pairs, and the SAME instances are used for every
  method and N.
- A calibration query is a paired rollout of S against the prefix on the same draw.

**Methods.** All output a set in F_R(P), with the same N and the same decision rule: edit only on a
positive Bonferroni-t LCB, otherwise keep the prefix.
- proxy (singleton importance);
- uniform over F_R;
- targeted (ambiguous repairs);
- adaptive (successive elimination).

Geometric floor (same instances): R = 0: 0.97, R = 1: 0.24, R = 2: 0.

Global regret, targeted calibration:

| N | 800 | 1,600 | 3,200 | 6,400 | 12,800 | 25,600 | 51,200 |
|---|---|---|---|---|---|---|---|
| R = 1 | 0.907 | 0.743 | 0.455 | 0.303 | **0.270** | 0.274 | 0.258 |
| R = 2 | 0.970 | 0.958 | 0.936 | 0.860 | **0.593** | 0.287 | **0.137** |

**Reading.** This is the two-cost law on a model with executable actors.
- More revision rights lower the floor (0.24 → 0) but need more calibration before they pay.
- R = 2 is worse than R = 1 up to about N ≈ 25k paired rollouts and better from 51k.
- The usable revision depth therefore depends on the calibration budget.
- Singleton-importance (proxy) acquisition never improves on the prefix at any N (R = 1: 0.97 →
  0.97). An interaction-blind acquisition cannot find repairs whose value lives in a pair.
- Targeted and uniform are close here, because the first-order margins are small. Almost every
  reachable repair is ambiguous, so targeting prunes little. Adaptive elimination is best at the
  largest N for R = 1 (0.245 against the 0.241 floor).
- No method is ever worse than the prefix beyond sampling noise, which is at most +0.006.

## What E1 establishes and what it does not

- **Establishes, on stated models:**
  - the T2 calibration law behaves as proved on its own class;
  - the symmetric-design starvation factor appears as proved;
  - in an executable Bayes-decoder task, the usable R depends on N, and interaction-blind proxy
    acquisition fails.
- **Does not establish:**
  - traffic benefit;
  - learnability from legal information in traffic (the Step 3 diagnostics are negative);
  - a proxy-OPTIMAL design (the symmetric design is a design, not the optimiser of a proxy
    criterion);
  - general MARL claims.
- **Limits:**
  - E1b is a single-pair interaction class, which is a special case of shared-pair interactions;
  - fixed g and β; one m and k;
  - the decision rule is a heuristic Bonferroni-t LCB, not a certified test for the non-Gaussian
    paired rewards.

## E1a-adaptive — two-stage screen-then-confirm (added 27/09, 20:10)

- **Producer:** `scripts/MARL_E1a_two_stage.py`, sha 5da21441…
- **Result:** `research/marl_budget/e1a_two_stage_20260927_194136/results.json`. Details and
  self-checks are in FULL_CORPUS_AUDIT §23.7.
- **Findings:**
  - On the exact needle model, the optimised two-stage design beats the proved lower bound for
    EVERY fixed schedule (`LeanMarlCalibrationGapV1.sched_calibration_lower`) once |Amb| ≥ 256
    (α = 0.05) or |Amb| ≥ 1024 (α = 0.01).
  - It stays within 3.6× of the adaptive null-world bound up to |Amb| = 65536.
- **Evidence class:** numerical; the adaptive upper bound is not a theorem.

## Corrections after MARL_E1_INDEPENDENT_AUDIT_20260927 (27/09, 22:30)

The artifacts are unchanged. These correct the claims made from them.

1. **E1b is NOT an instantiation of the Gaussian pair channel** (`LeanMarlPairCalibrationV1`
   assumes `rChan`).
   - E1b's paired squared-loss rewards have interaction-dependent HIGHER moments on queries that
     contain neither pair member. Audit witness: P = {0,1,2,3}, S = {0,1,2,4}, E = {0,8}. The mean
     difference is equal (−0.1), but the variance is 9.10 at null and 17.42 at the pair world.
   - E1b also has no null world.
   - E1b is therefore an **empirical extension with a matching MEAN value structure**. No KL or
     calibration lower bound transfers to it.
   - The mean-value realization is now proved separately: `LeanMarlE1bRealizationV1`,
     `ScoreLocal f g² β²`, with β²/2 under pair-shifted scores. It is numerically loose here
     (2η = 3.2 against 0.1 score steps).
2. **"R = 2 is worse than R = 1 until ~25k" is an algorithm result, not an intrinsic cost of
   rights.**
   - Since F₁ ⊂ F₂, an R2-capable learner can run the R1 algorithm.
   - The crossover comes from THIS full-pool calibration strategy: 24 candidates for R1 against
     114 for R2. With MIN_PER = 5 it returns P without sampling for N < 120 (R1) and N < 570 (R2).
   - Corrected reading: "this full-pool strategy needs more samples to exploit the larger family".
3. **Targeted and uniform are the SAME algorithm in E1b.** Every candidate passes the filter
   (24/24 and 114/114), not "almost every". Their curves differ only by random draws. It is a
   negative control, and no targeting benefit is shown.
4. **Proxy failure has limited scope.** It shows the failure of a mean-only singleton score policy.
   It is not an impossibility for algorithms using raw singleton observations, whose higher
   moments can carry interaction information.
5. **Adaptive curve: exploratory.**
   - Elimination can occur at 2 samples per candidate; MIN_PER only filters the final choice.
   - The plug-in variance has no time-uniform guarantee.
   - The Bonferroni-t decision rule remains a heuristic for mixture rewards.
6. **E1a counts.**
   - The grid N is nominal: each arm gets floor(N/M) samples, and the uniform-all-k-sets design
     also allocates to the free prefix dummy.
   - Threshold crossings come from 4000 trials, so they are estimates, not certified brackets.
   - "Linear in |Amb|" is too strong: β changes with R in this panel, and the fixed block cost has
     a log(M/α) factor.
7. **Two-stage decoder wording** is fixed in `scripts/MARL_E1a_two_stage_v2.py`.
   - Its formulas are exact for the FIRST-fired decoder (`rdec`) with the needle at the worst
     (last) index.
   - Its Monte-Carlo check now executes that decoder literally.
   - The rows are identical to v1 (`e1a_two_stage_v2_20260927_222919`).
