import Mathlib
import «LeanD6H3Exchange»

/-!
# Top-C surplus and Abel sign control

For a valid selected/rejected pairing Top-C gives the stronger pointwise
surplus inequality, hence every prefix sum is nonnegative in every ordering.
The Abel identity below turns those prefix inequalities into the sign needed
for a monotone weighted PAEC correction.
-/

namespace CIGAMF.P13.D6AbelSurplus

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6H3Exchange

noncomputable def prefixSum (z : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range r, z i

theorem prefixSum_succ (z : ℕ → ℝ) (r : ℕ) :
    prefixSum z (r + 1) = prefixSum z r + z r := by
  simp [prefixSum, Finset.sum_range_succ]

/- Finite Abel summation in the indexing used by a `d`-pair PAEC. -/
theorem abel_sum_identity (z beta : ℕ → ℝ) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), z i * beta i) =
      prefixSum z (d + 1) * beta d +
        ∑ i ∈ Finset.range d,
          prefixSum z (i + 1) * (beta i - beta (i + 1)) := by
  induction d with
  | zero =>
      simp [prefixSum]
  | succ d ih =>
      calc
        (∑ i ∈ Finset.range (d + 1 + 1), z i * beta i) =
            (∑ i ∈ Finset.range (d + 1), z i * beta i) +
              z (d + 1) * beta (d + 1) := by
                rw [Finset.sum_range_succ]
        _ = (prefixSum z (d + 1) * beta d +
              ∑ i ∈ Finset.range d,
                prefixSum z (i + 1) * (beta i - beta (i + 1))) +
              z (d + 1) * beta (d + 1) := by rw [ih]
        _ = prefixSum z (d + 1 + 1) * beta (d + 1) +
              ∑ i ∈ Finset.range (d + 1),
                prefixSum z (i + 1) * (beta i - beta (i + 1)) := by
              have hp : prefixSum z (d + 1 + 1) =
                  prefixSum z (d + 1) + z (d + 1) := by
                simpa [Nat.add_assoc] using prefixSum_succ z (d + 1)
              conv_rhs =>
                rhs
                rw [Finset.sum_range_succ]
              rw [hp]
              ring

theorem abel_weighted_sum_nonnegative
    (z beta : ℕ → ℝ) (d : ℕ)
    (hPrefix : ∀ r, r ≤ d + 1 → 0 ≤ prefixSum z r)
    (hBetaLast : 0 ≤ beta d)
    (hBetaMono : ∀ i, i < d → beta (i + 1) ≤ beta i) :
    0 ≤ ∑ i ∈ Finset.range (d + 1), z i * beta i := by
  rw [abel_sum_identity]
  apply add_nonneg
  · exact mul_nonneg (hPrefix (d + 1) le_rfl) hBetaLast
  · apply Finset.sum_nonneg
    intro i hi
    have hil : i < d := Finset.mem_range.mp hi
    exact mul_nonneg (hPrefix (i + 1) (by omega))
      (sub_nonneg.mpr (hBetaMono i hil))

theorem prefix_nonnegative_of_terms_nonnegative
    (z : ℕ → ℝ) (d : ℕ)
    (hz : ∀ i, i < d → 0 ≤ z i) :
    ∀ r, r ≤ d → 0 ≤ prefixSum z r := by
  intro r hr
  unfold prefixSum
  exact Finset.sum_nonneg fun i hi ↦ hz i (lt_of_lt_of_le (Finset.mem_range.mp hi) hr)

/- For Top-C, every selected/rejected pair is score ordered.  Consequently
the cyclic-permutation lemma is not needed merely to obtain nonnegative
prefix sums: any valid ordering of the pairs works. -/
theorem topK_paired_prefix_nonnegative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → ℝ) (selected : Finset ι) (k d : ℕ)
    (hTop : IsTopKByScore C selected k)
    (s t : Fin d → ι)
    (hs : ∀ a, s a ∈ selected)
    (ht : ∀ a, t a ∉ selected) :
    ∀ r, r ≤ d →
      0 ≤ ∑ a ∈ Finset.univ.filter (fun a : Fin d ↦ a.val < r),
        (C (s a) - C (t a)) := by
  intro r hr
  apply Finset.sum_nonneg
  intro a ha
  exact sub_nonneg.mpr
    (topK_pairwise_score_order C selected k hTop (hs a) (ht a))

noncomputable def abelCorrection (z beta : ℕ → ℝ) (d : ℕ) : ℝ :=
  -(∑ i ∈ Finset.range (d + 1), z i * beta i)

theorem abelCorrection_nonpositive
    (z beta : ℕ → ℝ) (d : ℕ)
    (hPrefix : ∀ r, r ≤ d + 1 → 0 ≤ prefixSum z r)
    (hBetaLast : 0 ≤ beta d)
    (hBetaMono : ∀ i, i < d → beta (i + 1) ≤ beta i) :
    abelCorrection z beta d ≤ 0 := by
  unfold abelCorrection
  exact neg_nonpos.mpr
    (abel_weighted_sum_nonnegative z beta d hPrefix hBetaLast hBetaMono)

end CIGAMF.P13.D6AbelSurplus
