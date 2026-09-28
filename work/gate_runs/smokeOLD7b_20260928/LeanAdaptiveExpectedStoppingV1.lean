import «LeanAdaptiveStoppingTailV1»

/-! # Adaptive A5: the layer-cake identity PROVED, and the concentration input DISCHARGED.

`LeanAdaptiveStoppingTailV1` bounds `∑_n P(τ > n)` by a geometric tail and says, in its
own header, that the step from that sum to `E[τ]` is the standard layer-cake fact and is
CITED, not proved.  It also names a per-`(arm, count)` concentration inequality as an
input it does not supply.  Both are closed here.

## 1. THE LAYER-CAKE IDENTITY, PROVED

`lintegral_nat_eq_tsum_meas_gt`: for an `ℕ`-valued stopping time,

    ∫⁻ τ dμ = ∑'_{n} μ {τ > n},

proved by writing `τ ω` as the sum of the indicators of `{n < τ}` and exchanging the sum
with the integral (`lintegral_tsum`).  No continuous layer-cake machinery and no citation.
`expected_stopping_le` then converts the existing geometric tail bound into a bound on the
EXPECTED stopping time, which is what the audit asked for.

## 2. THE CONCENTRATION INPUT, DISCHARGED

`subgaussian_threshold`: if the per-`(arm, count)` deviation is sub-Gaussian with
parameter `c` -- which Gaussian noise is -- then the threshold `√(2c log(1/β))` has
deviation probability at most `β`.  Feeding `β = δ/(K n(n+1))` into `peeling_budget` of
the previous file therefore gives `P(Eᶜ) ≤ δ` with NO assumed inequality: the bound comes
from `ProbabilityTheory.HasSubgaussianMGF.measure_ge_le`.

## WHAT THIS DOES NOT ESTABLISH

- The TRACKING step -- that the allocation actually realises the intended per-arm counts
  -- remains open.  A5 is not fully closed by this file; its probabilistic inputs are.
- `subgaussian_threshold` assumes the deviation is sub-Gaussian with a KNOWN parameter
  `c`.  With an estimated variance that hypothesis is not automatic, and the manuscript
  must say which regime it is in.
- The geometric tail `P(τ > n) ≤ C ρⁿ` is still a hypothesis of `expected_stopping_le`,
  supplied by the algorithm's analysis, not proved here.
-/

namespace CIGAMF.P13.AdaptiveExpectedStopping

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The layer-cake identity for an `ℕ`-valued stopping time, proved.**
`∫⁻ τ dμ = ∑'_n μ {τ > n}`. -/
theorem lintegral_nat_eq_tsum_meas_gt (μ : Measure Ω) (tau : Ω → ℕ)
    (hmeas : Measurable tau) :
    ∫⁻ ω, (tau ω : ℝ≥0∞) ∂μ = ∑' n : ℕ, μ {ω | n < tau ω} := by
  classical
  have hset : ∀ n : ℕ, MeasurableSet {ω | n < tau ω} := fun n =>
    hmeas (measurableSet_lt measurable_const measurable_id)
  have hpt : ∀ ω : Ω, (tau ω : ℝ≥0∞)
      = ∑' n : ℕ, Set.indicator {ω' | n < tau ω'} (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [tsum_eq_sum (s := Finset.range (tau ω))]
    · have hone : ∀ n ∈ Finset.range (tau ω),
          Set.indicator {ω' | n < tau ω'} (fun _ => (1 : ℝ≥0∞)) ω = 1 := by
        intro n hn
        have : n < tau ω := Finset.mem_range.mp hn
        simp [Set.indicator_apply, this]
      rw [Finset.sum_congr rfl hone]
      simp
    · intro n hn
      have : ¬ n < tau ω := by simpa using hn
      simp [Set.indicator_apply, this]
  calc ∫⁻ ω, (tau ω : ℝ≥0∞) ∂μ
      = ∫⁻ ω, ∑' n : ℕ, Set.indicator {ω' | n < tau ω'} (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
        exact lintegral_congr fun ω => hpt ω
    _ = ∑' n : ℕ, ∫⁻ ω, Set.indicator {ω' | n < tau ω'} (fun _ => (1 : ℝ≥0∞)) ω ∂μ :=
        lintegral_tsum fun n => ((measurable_const.indicator (hset n)).aemeasurable)
    _ = ∑' n : ℕ, μ {ω | n < tau ω} := by
        refine tsum_congr fun n => ?_
        rw [lintegral_indicator (hset n)]
        simp

/-- **The expected stopping time, bounded.**  With the layer-cake identity proved above,
a geometric tail bounds `E[τ]` itself, not merely the tail sum. -/
theorem expected_stopping_le (μ : Measure Ω) (tau : Ω → ℕ) (hmeas : Measurable tau)
    (C rho : ℝ≥0∞) (hrho : rho < 1)
    (htail : ∀ n : ℕ, μ {ω | n < tau ω} ≤ C * rho ^ n) :
    ∫⁻ ω, (tau ω : ℝ≥0∞) ∂μ ≤ C * (1 - rho)⁻¹ := by
  rw [lintegral_nat_eq_tsum_meas_gt μ tau hmeas]
  calc ∑' n : ℕ, μ {ω | n < tau ω}
      ≤ ∑' n : ℕ, C * rho ^ n := ENNReal.tsum_le_tsum htail
    _ = C * (1 - rho)⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- **The concentration input, discharged.**  A sub-Gaussian deviation with parameter `c`
meets any budget `β ∈ (0,1]` at the threshold `√(2c log(1/β))`.  This is what
`peeling_budget` needs at each `(arm, count)`; nothing is assumed. -/
theorem subgaussian_threshold {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    {c : ℝ≥0} (hc : (0:ℝ) < (c : ℝ)) (h : HasSubgaussianMGF X c μ)
    (beta : ℝ) (hb0 : 0 < beta) (hb1 : beta ≤ 1) :
    μ.real {ω | Real.sqrt (2 * (c : ℝ) * Real.log (1 / beta)) ≤ X ω} ≤ beta := by
  have hL : 0 ≤ Real.log (1 / beta) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hb0]
    linarith
  have harg : 0 ≤ 2 * (c : ℝ) * Real.log (1 / beta) := by positivity
  have heps : 0 ≤ Real.sqrt (2 * (c : ℝ) * Real.log (1 / beta)) := Real.sqrt_nonneg _
  have hbound := h.measure_ge_le heps
  have hsq : Real.sqrt (2 * (c : ℝ) * Real.log (1 / beta)) ^ 2
      = 2 * (c : ℝ) * Real.log (1 / beta) := Real.sq_sqrt harg
  rw [hsq] at hbound
  have hcne : (c : ℝ) ≠ 0 := ne_of_gt hc
  have hdiv : -(2 * (c : ℝ) * Real.log (1 / beta)) / (2 * (c : ℝ))
      = -Real.log (1 / beta) := by
    field_simp
  rw [hdiv] at hbound
  have hexp : Real.exp (-Real.log (1 / beta)) = beta := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rwa [hexp] at hbound

#print axioms lintegral_nat_eq_tsum_meas_gt
#print axioms expected_stopping_le
#print axioms subgaussian_threshold

end CIGAMF.P13.AdaptiveExpectedStopping
