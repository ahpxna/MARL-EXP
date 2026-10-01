import Mathlib

/-! # Structural: the mechanism that makes the average/execution gap EQUAL the number
of budgets.

`LeanStructuralAvgPathGapV1` proves the sandwich `avgVal ≤ pathVal ≤ b·avgVal` and
the saturation lemma `epsNest ≤ b·avgVal`.  `scripts/P3_avg_path_amplification.py`
exhibits an explicit family with ratio exactly `b = m-1` for `m = 5..14` and shows by
exhaustive search that `b` is the best available at every `m ≤ 7`.  What was missing
is WHY: the two conditions the search reports (the cheapest ordering puts all its
regret on ONE budget, and the uniform dual is optimal).  Those are proved here, in
general, as the mechanism -- so the family's numbers are an instance of a theorem
rather than a table.

## WHAT IS PROVED

* `max_le_sum` — for non-negative regret the per-ordering maximum is at most the sum.
* `sum_eq_max_of_concentrated` — and they are EQUAL exactly when the regret is
  carried by one budget: if `r k₀ = M` and `r k = 0` off `k₀`, the sum is `M`.
* `path_le_sum_expect` — `pathVal ≤ ∑_k E_P r_k`, the step the `b` factor comes from.
* `avg_eq_of_balanced` — if every budget has the same expectation `e`, then
  `avgVal = e`, so `∑_k E_P r_k = b·avgVal`.
* `ratio_card_of_concentrated_and_balanced` — the two together: concentrated regret
  plus balanced budgets force `pathVal = b·avgVal`, the saturating case.

## WHAT THIS DOES NOT ESTABLISH

- That the explicit family `g_m = (-3, -1^…, +1^…, 3)` satisfies the two hypotheses
  for every `m` is checked in exact rationals by the script for `m = 5..14`; it is
  not proved here.  A proof would be a prefix-counting argument on that family and
  is the natural next step.
- `r` is an arbitrary non-negative function; nothing ties it to `selectedRadius`.
-/

namespace CIGAMF.P13.StructuralSaturation

open Finset

noncomputable section

variable {Ord Bud : Type*} [Fintype Ord] [Fintype Bud] [Nonempty Ord] [Nonempty Bud]

theorem max_le_sum (r : Bud → ℝ) (hr : ∀ k, 0 ≤ r k) :
    (univ : Finset Bud).sup' univ_nonempty r ≤ ∑ k, r k :=
  Finset.sup'_le _ _ fun k _ => Finset.single_le_sum (fun j _ => hr j) (mem_univ k)

theorem sum_eq_max_of_concentrated [DecidableEq Bud] (r : Bud → ℝ) (k₀ : Bud)
    (hzero : ∀ k, k ≠ k₀ → r k = 0) :
    ∑ k, r k = r k₀ := by
  classical
  refine Finset.sum_eq_single k₀ (fun k _ hk => hzero k hk) (fun h => ?_)
  exact absurd (mem_univ k₀) h

theorem path_le_sum_expect (r : Ord → Bud → ℝ) (P : Ord → ℝ)
    (hr : ∀ pi k, 0 ≤ r pi k) (hP : ∀ pi, 0 ≤ P pi) :
    (∑ pi, P pi * ((univ : Finset Bud).sup' univ_nonempty (fun k => r pi k)))
      ≤ ∑ k, ∑ pi, P pi * r pi k := by
  have step : (∑ pi, P pi * ((univ : Finset Bud).sup' univ_nonempty (fun k => r pi k)))
      ≤ ∑ pi, P pi * (∑ k, r pi k) :=
    Finset.sum_le_sum fun pi _ =>
      mul_le_mul_of_nonneg_left (max_le_sum (fun k => r pi k) (hr pi)) (hP pi)
  have swap : ∑ pi, P pi * (∑ k, r pi k) = ∑ k, ∑ pi, P pi * r pi k := by
    have inner : ∀ pi : Ord, P pi * (∑ k, r pi k) = ∑ k, P pi * r pi k :=
      fun pi => Finset.mul_sum _ _ _
    simp_rw [inner]
    exact Finset.sum_comm
  linarith [step, swap ▸ step]

theorem avg_eq_of_balanced (r : Ord → Bud → ℝ) (P : Ord → ℝ) (e : ℝ)
    (hbal : ∀ k, (∑ pi, P pi * r pi k) = e) :
    (univ : Finset Bud).sup' univ_nonempty (fun k => ∑ pi, P pi * r pi k) = e := by
  simp only [hbal]
  exact le_antisymm (Finset.sup'_le _ _ fun k _ => le_rfl)
    (Finset.le_sup' (fun _ : Bud => e) (mem_univ (Classical.arbitrary Bud)))

/-- The saturating case, in general. -/
theorem ratio_card_of_concentrated_and_balanced
    (r : Ord → Bud → ℝ) (P : Ord → ℝ) (e : ℝ)
    (hr : ∀ pi k, 0 ≤ r pi k) (hP : ∀ pi, 0 ≤ P pi)
    (hbal : ∀ k, (∑ pi, P pi * r pi k) = e)
    (hconc : ∀ pi, (∑ k, r pi k)
      = (univ : Finset Bud).sup' univ_nonempty (fun k => r pi k)) :
    (∑ pi, P pi * ((univ : Finset Bud).sup' univ_nonempty (fun k => r pi k)))
      = (Fintype.card Bud : ℝ)
        * (univ : Finset Bud).sup' univ_nonempty (fun k => ∑ pi, P pi * r pi k) := by
  have hswap : ∑ pi, P pi * (∑ k, r pi k) = ∑ k, ∑ pi, P pi * r pi k := by
    have inner : ∀ pi : Ord, P pi * (∑ k, r pi k) = ∑ k, P pi * r pi k :=
      fun pi => Finset.mul_sum _ _ _
    simp_rw [inner]
    exact Finset.sum_comm
  have hleft : (∑ pi, P pi * ((univ : Finset Bud).sup' univ_nonempty (fun k => r pi k)))
      = ∑ pi, P pi * (∑ k, r pi k) := by
    refine Finset.sum_congr rfl fun pi _ => ?_
    rw [hconc pi]
  have hright : ∑ k, ∑ pi, P pi * r pi k = (Fintype.card Bud : ℝ) * e := by
    simp only [hbal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hleft, hswap, hright, avg_eq_of_balanced r P e hbal]

#print axioms max_le_sum
#print axioms sum_eq_max_of_concentrated
#print axioms path_le_sum_expect
#print axioms avg_eq_of_balanced
#print axioms ratio_card_of_concentrated_and_balanced

end
end CIGAMF.P13.StructuralSaturation
