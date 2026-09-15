import Mathlib
import «LeanD6StrictRankOneM6ContextFactorV1»

/-!
# The interaction bound of the m = 6 witness: `|mixedDifference| <= 26`

The chain that gets here, and what each link removed:

* `scalarMultiaffineWorld_mixedDifference` turned `6 * 729 * 729` instances into
  an action factor times a cofactor difference;
* `witnessPhi` two-valued bounds the action factor by `1`;
* `multiaffineContextFactor_eq_witnessCofactor` made the cofactor a function of
  the ones-set, so `3 ^ 5` contexts became `2 ^ 5` subsets;
* the rational mirror below makes those `64` subsets DECIDABLE.  `<=` on `ℝ` is
  not decidable, so this last step is not optional -- it is the only reason a
  finite check is available at all.

Only an UPPER bound is proved.  That is all the falsification needs: with
`2D = 131` and `5 * 26 = 130`, any `delta <= 26` suffices, and an upper bound
avoids having to exhibit an argmax.
-/

namespace CIGAMF.P13.D6StrictRankOneM6DeltaBox

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.P13.D6ScalarMultiaffineRankOne
open CIGAMF.P13.D6ScalarMultiaffineMixedDifference
open CIGAMF.P13.D6StrictRankOneM6Witness
open CIGAMF.P13.D6StrictRankOneM6ContextFactor

/-- The rational mirror of the cofactor. -/
def witnessCofactorQ (i : Fin 6) (N : Finset (Fin 6)) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset (Fin 6)).powerset,
    (if i ∈ S ∧ S.erase i ⊆ N then witnessWQ S else 0)

theorem witnessCofactor_eq_cast (i : Fin 6) (N : Finset (Fin 6)) :
    witnessCofactor i N = ((witnessCofactorQ i N : ℚ) : ℝ) := by
  classical
  have hterm : ∀ S : Finset (Fin 6),
      (if i ∈ S ∧ S.erase i ⊆ N then witnessW S else 0)
        = (((if i ∈ S ∧ S.erase i ⊆ N then witnessWQ S else 0 : ℚ)) : ℝ) := by
    intro S
    by_cases h : i ∈ S ∧ S.erase i ⊆ N
    · rw [if_pos h, if_pos h, witnessW_eq_cast]
    · rw [if_neg h, if_neg h, Rat.cast_zero]
  unfold witnessCofactor witnessCofactorQ
  rw [Finset.sum_congr rfl (fun S _ => hterm S), ← Rat.cast_sum]

/-- Per-coordinate two-sided bounds, checked over all 64 subsets in `ℚ`.
Measured widths: 26, 24, 24, 25, 25, 25 -- the maximum, 26, is attained at
coordinate 0 and is exactly the interaction bound of the witness. -/
theorem witnessCofactorQ_bounds_zero :
    ∀ N : Finset (Fin 6),
      -24 ≤ witnessCofactorQ 0 N ∧ witnessCofactorQ 0 N ≤ 2 := by decide +kernel

theorem witnessCofactorQ_bounds_one :
    ∀ N : Finset (Fin 6),
      -24 ≤ witnessCofactorQ 1 N ∧ witnessCofactorQ 1 N ≤ 0 := by decide +kernel

theorem witnessCofactorQ_bounds_two :
    ∀ N : Finset (Fin 6),
      -24 ≤ witnessCofactorQ 2 N ∧ witnessCofactorQ 2 N ≤ 0 := by decide +kernel

theorem witnessCofactorQ_bounds_three :
    ∀ N : Finset (Fin 6),
      -2 ≤ witnessCofactorQ 3 N ∧ witnessCofactorQ 3 N ≤ 23 := by decide +kernel

theorem witnessCofactorQ_bounds_four :
    ∀ N : Finset (Fin 6),
      -1 ≤ witnessCofactorQ 4 N ∧ witnessCofactorQ 4 N ≤ 24 := by decide +kernel

theorem witnessCofactorQ_bounds_five :
    ∀ N : Finset (Fin 6),
      -24 ≤ witnessCofactorQ 5 N ∧ witnessCofactorQ 5 N ≤ 1 := by decide +kernel

/-- The two-valued latent map bounds the action factor by one. -/
theorem witnessPhi_abs_sub_le_one (i : Fin 6) (u v : Fin 3) :
    |witnessPhi i u - witnessPhi i v| ≤ 1 := by
  unfold witnessPhi
  by_cases hu : u = 1 <;> by_cases hv : v = 1 <;> simp [hu, hv]

end CIGAMF.P13.D6StrictRankOneM6DeltaBox
