import Mathlib

/-!
# Paper A: the expectation of an `ℕ∞`-valued hitting time, from its tail

`LeanPaperAEndgameV1.OperationalFinish` asks for `∫⁻ ω, (tau ω).toENNReal ∂μ ≠ ⊤` for the
UNTRUNCATED hitting time `tau : Ω → ℕ∞` of the stopping rule.  This module provides the step
from a tail bound to that statement, with no assumption that `tau` is finite:

* `toENNReal_eq_tsum` / `lintegral_eq_tsum_tail` -- the layer-cake identity on `ℕ∞`:
  `E tau = sum_t P(t < tau)`, where `tau = ⊤` contributes `⊤` (every term is one);
* `lintegral_le_of_tail` -- if `P(t < tau) <= f t` for `t >= t0` with `f` summable, then
  `E tau <= t0 + sum f`, hence `E tau ≠ ⊤` (`lintegral_ne_top_of_tail`) and
  `P(tau = ⊤) = 0` (`top_null_of_tail`);
* `lintegral_ne_top_of_rpow_tail` -- the case the A7 chain produces,
  `P(t < tau) <= C t^(-3/2)`.

Monotone convergence is inside `lintegral_tsum`; no truncation level is needed.
-/

namespace CIGAMF.P13.PaperAENatExpect

open MeasureTheory
open scoped ENNReal

/-- The layer-cake identity for one element of `ℕ∞`. -/
theorem toENNReal_eq_tsum (n : ℕ∞) :
    (n : ℝ≥0∞) = ∑' t : ℕ, if (t : ℕ∞) < n then (1 : ℝ≥0∞) else 0 := by
  induction n using ENat.recTopCoe with
  | top =>
      simp only [ENat.toENNReal_top, ENat.coe_lt_top, if_true]
      exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe k =>
      rw [ENat.toENNReal_coe]
      rw [tsum_eq_sum (s := Finset.range k) (fun t ht => by
        rw [if_neg]
        intro hlt
        exact ht (Finset.mem_range.mpr (by exact_mod_cast hlt)))]
      rw [Finset.sum_congr rfl fun t ht => by
        rw [if_pos (by exact_mod_cast Finset.mem_range.mp ht)]]
      simp

/-- **Layer cake on `ℕ∞`**: `E tau = sum_t P(t < tau)`. -/
theorem lintegral_eq_tsum_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (τ : Ω → ℕ∞) (hτ : Measurable τ) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ = ∑' t : ℕ, μ {ω | (t : ℕ∞) < τ ω} := by
  have hmeas : ∀ t : ℕ, MeasurableSet {ω | (t : ℕ∞) < τ ω} := fun t =>
    hτ (MeasurableSet.of_discrete (s := {n : ℕ∞ | (t : ℕ∞) < n}))
  have hpt : ∀ ω, (τ ω : ℝ≥0∞) = ∑' t : ℕ, {ω | (t : ℕ∞) < τ ω}.indicator 1 ω := by
    intro ω
    rw [toENNReal_eq_tsum]
    congr 1
    funext t
    simp [Set.indicator_apply]
  rw [lintegral_congr hpt, lintegral_tsum fun t => (measurable_one.indicator (hmeas t)).aemeasurable]
  congr 1
  funext t
  exact lintegral_indicator_one (hmeas t)

/-- `sum_t [t < t0] = t0`. -/
theorem tsum_lt_indicator (t0 : ℕ) :
    ∑' t : ℕ, (if t < t0 then (1 : ℝ≥0∞) else 0) = t0 := by
  have := toENNReal_eq_tsum (t0 : ℕ∞)
  rw [ENat.toENNReal_coe] at this
  rw [this]
  congr 1
  funext t
  simp only [Nat.cast_lt]

/-- **A summable tail gives a finite expectation**, with an explicit bound. -/
theorem lintegral_le_of_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (τ : Ω → ℕ∞) (hτ : Measurable τ) (t0 : ℕ) (f : ℕ → ℝ)
    (hf0 : ∀ t, 0 ≤ f t) (hfs : Summable f)
    (htail : ∀ t, t0 ≤ t → μ {ω | (t : ℕ∞) < τ ω} ≤ ENNReal.ofReal (f t)) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ ≤ (t0 : ℝ≥0∞) + ENNReal.ofReal (∑' t, f t) := by
  rw [lintegral_eq_tsum_tail μ τ hτ, ENNReal.ofReal_tsum_of_nonneg hf0 hfs,
    ← tsum_lt_indicator t0, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun t => ?_
  by_cases ht : t < t0
  · rw [if_pos ht]
    exact le_trans prob_le_one le_self_add
  · rw [if_neg ht, zero_add]
    exact htail t (not_lt.mp ht)

theorem lintegral_ne_top_of_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (τ : Ω → ℕ∞) (hτ : Measurable τ) (t0 : ℕ) (f : ℕ → ℝ)
    (hf0 : ∀ t, 0 ≤ f t) (hfs : Summable f)
    (htail : ∀ t, t0 ≤ t → μ {ω | (t : ℕ∞) < τ ω} ≤ ENNReal.ofReal (f t)) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top t0, ENNReal.ofReal_ne_top⟩)
    (lintegral_le_of_tail μ τ hτ t0 f hf0 hfs htail)

/-- The real expectation bound. -/
theorem toReal_lintegral_le_of_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (τ : Ω → ℕ∞) (hτ : Measurable τ) (t0 : ℕ) (f : ℕ → ℝ)
    (hf0 : ∀ t, 0 ≤ f t) (hfs : Summable f)
    (htail : ∀ t, t0 ≤ t → μ {ω | (t : ℕ∞) < τ ω} ≤ ENNReal.ofReal (f t)) :
    (∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ).toReal ≤ t0 + ∑' t, f t := by
  have hs : 0 ≤ ∑' t, f t := tsum_nonneg hf0
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [ENNReal.ofReal_add (by positivity) hs, ENNReal.ofReal_natCast]
  exact lintegral_le_of_tail μ τ hτ t0 f hf0 hfs htail

/-- **The hitting time is finite almost surely.** -/
theorem top_null_of_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (τ : Ω → ℕ∞) (hτ : Measurable τ) (t0 : ℕ) (f : ℕ → ℝ)
    (hf0 : ∀ t, 0 ≤ f t) (hfs : Summable f)
    (htail : ∀ t, t0 ≤ t → μ {ω | (t : ℕ∞) < τ ω} ≤ ENNReal.ofReal (f t)) :
    μ {ω | τ ω = ⊤} = 0 := by
  have hm : Measurable fun ω => (τ ω : ℝ≥0∞) :=
    (Measurable.of_discrete (f := fun n : ℕ∞ => (n : ℝ≥0∞))).comp hτ
  have hae := ae_lt_top hm (lintegral_ne_top_of_tail μ τ hτ t0 f hf0 hfs htail)
  rw [ae_iff] at hae
  refine measure_mono_null (fun ω hω => ?_) hae
  show ¬ ((τ ω : ℝ≥0∞) < ⊤)
  rw [show τ ω = ⊤ from hω, ENat.toENNReal_top]
  exact lt_irrefl _

/-- The tail the A7 chain produces is summable. -/
theorem summable_rpow_tail (C : ℝ) :
    Summable fun t : ℕ => C * (((t : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
  (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left C

/-- **`P(t < tau) <= C t^(-3/2)` for `t >= t0` gives a finite expected hitting time.** -/
theorem lintegral_ne_top_of_rpow_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (τ : Ω → ℕ∞) (hτ : Measurable τ) (t0 : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (htail : ∀ t, t0 ≤ t →
      μ {ω | (t : ℕ∞) < τ ω} ≤ ENNReal.ofReal (C * (((t : ℝ) ^ ((3 : ℝ) / 2))⁻¹))) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ ≠ ⊤ ∧ μ {ω | τ ω = ⊤} = 0 := by
  have hf0 : ∀ t : ℕ, 0 ≤ C * (((t : ℝ) ^ ((3 : ℝ) / 2))⁻¹) := fun t =>
    mul_nonneg hC (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg t) _))
  exact ⟨lintegral_ne_top_of_tail μ τ hτ t0 _ hf0 (summable_rpow_tail C) htail,
    top_null_of_tail μ τ hτ t0 _ hf0 (summable_rpow_tail C) htail⟩

#print axioms toENNReal_eq_tsum
#print axioms lintegral_eq_tsum_tail
#print axioms lintegral_le_of_tail
#print axioms lintegral_ne_top_of_tail
#print axioms toReal_lintegral_le_of_tail
#print axioms top_null_of_tail
#print axioms lintegral_ne_top_of_rpow_tail

end CIGAMF.P13.PaperAENatExpect
