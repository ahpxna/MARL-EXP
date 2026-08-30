import Mathlib
import «LeanFunctionalBoundaryV4»

/-! Auxiliary deterministic results for split evaluation and continuous
query-targeted allocation. -/

namespace CIGAMF.V4.FunctionalAux

open scoped BigOperators
open SupportGeometry FunctionalBoundary

section SplitEvaluation

variable {A Sel Eval : Type*} [Fintype A] [Nonempty A]
variable [Fintype Eval]

noncomputable def evalMean (p : Eval → ℝ) (Qhat : Eval → A → ℝ) (a : A) : ℝ :=
  Finset.univ.sum (fun e => p e * Qhat e a)

noncomputable def splitSelectedContrastMean
    (p : Eval → ℝ) (Qhat : Eval → A → ℝ)
    (aPlus aMinus : Sel → A) (s : Sel) : ℝ :=
  evalMean p Qhat (aPlus s) - evalMean p Qhat (aMinus s)

theorem A5_split_estimator_targets_selected_contrast
    (p : Eval → ℝ) (Qhat : Eval → A → ℝ) (Q : A → ℝ)
    (aPlus aMinus : Sel → A)
    (hpNonneg : ∀ e, 0 ≤ p e) (hpOne : Finset.univ.sum p = 1)
    (hUnbiased : ∀ a, evalMean p Qhat a = Q a)
    (s : Sel) :
    splitSelectedContrastMean p Qhat aPlus aMinus s =
      Q (aPlus s) - Q (aMinus s) := by
  rw [splitSelectedContrastMean, hUnbiased, hUnbiased]

theorem A5_selected_contrast_le_capacity
    (Q : A → ℝ) (aPlus aMinus : A) :
    Q aPlus - Q aMinus ≤ capacity Q := by
  simp only [capacity, osc]
  linarith [le_maxVal Q aPlus, minVal_le Q aMinus]

theorem A5_split_mean_le_true_capacity
    (p : Eval → ℝ) (Qhat : Eval → A → ℝ) (Q : A → ℝ)
    (aPlus aMinus : Sel → A)
    (hpNonneg : ∀ e, 0 ≤ p e) (hpOne : Finset.univ.sum p = 1)
    (hUnbiased : ∀ a, evalMean p Qhat a = Q a)
    (s : Sel) :
    splitSelectedContrastMean p Qhat aPlus aMinus s ≤ capacity Q := by
  rw [A5_split_estimator_targets_selected_contrast p Qhat Q aPlus aMinus
    hpNonneg hpOne hUnbiased s]
  exact A5_selected_contrast_le_capacity Q (aPlus s) (aMinus s)

end SplitEvaluation

section ContinuousAllocation

variable {A : Type*} [Fintype A] [Nonempty A]

noncomputable def allocationVariance (c n : A → ℝ) : ℝ :=
  Finset.univ.sum (fun a => (c a) ^ 2 / n a)

noncomputable def continuousNeyman (c : A → ℝ) (N : ℝ) (a : A) : ℝ :=
  N * c a / Finset.univ.sum c

theorem A6_cauchy_lower_bound
    (c n : A → ℝ) (N : ℝ)
    (hnPos : ∀ a, 0 < n a) (hnTotal : Finset.univ.sum n = N) :
    (Finset.univ.sum c) ^ 2 / N ≤ allocationVariance c n := by
  have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ c
    (fun a _ => hnPos a)
  simpa [allocationVariance, hnTotal] using h

theorem continuousNeyman_pos
    (c : A → ℝ) (N : ℝ) (hcPos : ∀ a, 0 < c a) (hN : 0 < N) (a : A) :
    0 < continuousNeyman c N a := by
  have hsum : 0 < Finset.univ.sum c :=
    Finset.sum_pos (fun a _ => hcPos a) Finset.univ_nonempty
  exact div_pos (mul_pos hN (hcPos a)) hsum

theorem continuousNeyman_total
    (c : A → ℝ) (N : ℝ) (hcPos : ∀ a, 0 < c a) :
    Finset.univ.sum (continuousNeyman c N) = N := by
  have hsum : Finset.univ.sum c ≠ 0 := ne_of_gt <|
    Finset.sum_pos (fun a _ => hcPos a) Finset.univ_nonempty
  unfold continuousNeyman
  calc
    Finset.univ.sum (fun a => N * c a / Finset.univ.sum c) =
        N * Finset.univ.sum c / Finset.univ.sum c := by
      rw [Finset.mul_sum]
      simp only [Finset.sum_div]
    _ = N := by field_simp

theorem continuousNeyman_zero_coefficient
    (c : A → ℝ) (N : ℝ) (a : A)
    (hSum : Finset.univ.sum c ≠ 0) (hca : c a = 0) :
    continuousNeyman c N a = 0 := by
  simp [continuousNeyman, hca]

theorem continuousNeyman_nonneg
    (c : A → ℝ) (N : ℝ)
    (hc : ∀ a, 0 ≤ c a) (hSum : 0 < Finset.univ.sum c) (hN : 0 ≤ N)
    (a : A) : 0 ≤ continuousNeyman c N a := by
  unfold continuousNeyman
  exact div_nonneg (mul_nonneg hN (hc a)) hSum.le

theorem continuousNeyman_variance
    (c : A → ℝ) (N : ℝ) (hcPos : ∀ a, 0 < c a) (hN : 0 < N) :
    allocationVariance c (continuousNeyman c N) =
      (Finset.univ.sum c) ^ 2 / N := by
  have hsum : Finset.univ.sum c ≠ 0 := ne_of_gt <|
    Finset.sum_pos (fun a _ => hcPos a) Finset.univ_nonempty
  have hN0 : N ≠ 0 := ne_of_gt hN
  unfold allocationVariance continuousNeyman
  calc
    Finset.univ.sum (fun a => c a ^ 2 / (N * c a / Finset.univ.sum c)) =
        Finset.univ.sum (fun a => c a * Finset.univ.sum c / N) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hca : c a ≠ 0 := ne_of_gt (hcPos a)
      field_simp
    _ = (Finset.univ.sum c) ^ 2 / N := by
      calc
        Finset.univ.sum (fun a => c a * Finset.univ.sum c / N) =
            (Finset.univ.sum (fun a => c a * Finset.univ.sum c)) / N := by
          exact (Finset.sum_div (s := Finset.univ)
            (f := fun a => c a * Finset.univ.sum c) N).symm
        _ = (Finset.univ.sum c) ^ 2 / N := by
          rw [← Finset.sum_mul]
          ring

theorem A6_continuous_neyman_optimal
    (c n : A → ℝ) (N : ℝ)
    (hcPos : ∀ a, 0 < c a) (hN : 0 < N)
    (hnPos : ∀ a, 0 < n a) (hnTotal : Finset.univ.sum n = N) :
    allocationVariance c (continuousNeyman c N) ≤ allocationVariance c n := by
  rw [continuousNeyman_variance c N hcPos hN]
  exact A6_cauchy_lower_bound c n N hnPos hnTotal

theorem A6_query_weight_allocation
    (w sigma n : A → ℝ) (N : ℝ)
    (hcPos : ∀ a, 0 < |w a| * sigma a) (hN : 0 < N)
    (hnPos : ∀ a, 0 < n a) (hnTotal : Finset.univ.sum n = N) :
    allocationVariance (fun a => |w a| * sigma a)
        (continuousNeyman (fun a => |w a| * sigma a) N) ≤
      allocationVariance (fun a => |w a| * sigma a) n := by
  exact A6_continuous_neyman_optimal (fun a => |w a| * sigma a) n N
    hcPos hN hnPos hnTotal

end ContinuousAllocation

end CIGAMF.V4.FunctionalAux
