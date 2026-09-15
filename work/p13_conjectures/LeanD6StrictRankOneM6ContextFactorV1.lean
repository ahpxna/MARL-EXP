import Mathlib
import «LeanD6ScalarMultiaffineMixedDifferenceV1»
import «LeanD6StrictRankOneM6WitnessV1»

/-!
# The coordinate cofactor of the m = 6 witness depends only on the ones-set

`witnessPhi` is the indicator of action `1`, so a product of `phi` over a set of
coordinates is `1` exactly when every one of those coordinates is playing action
`1`, and `0` otherwise.  The cofactor therefore does not see the context `z` at
all -- only the SET of coordinates where `z` is `1`.

That collapses the finite work still ahead from `3 ^ 5 = 243` contexts per
coordinate to `2 ^ 5 = 32`, and it turns a statement about functions
`Fin 6 -> Fin 3` into a statement about `Finset (Fin 6)`, which is a `Fintype`
and therefore reachable by decision procedures once the values are rational.

Only the reduction is proved here.  The numeric bounds on `witnessCofactor` are
NOT stated in this file: they need the rational mirror, and a bound asserted
before it can be checked is worse than a bound that is absent.
-/

namespace CIGAMF.P13.D6StrictRankOneM6ContextFactor

open scoped BigOperators
open CIGAMF.P13.D6ScalarMultiaffineRankOne
open CIGAMF.P13.D6StrictRankOneM6Witness

/-- The coordinates on which a context plays the latent-active action. -/
def onesSet (z : Fin 6 → Fin 3) : Finset (Fin 6) :=
  Finset.univ.filter (fun j => z j = 1)

theorem mem_onesSet_iff (z : Fin 6 → Fin 3) (j : Fin 6) :
    j ∈ onesSet z ↔ z j = 1 := by
  classical
  simp [onesSet]

/-- A product of two-valued `phi` over a coordinate set is the indicator of that
set being contained in the ones-set. -/
theorem witnessPhi_prod (S : Finset (Fin 6)) (z : Fin 6 → Fin 3) :
    (∏ j ∈ S, witnessPhi j (z j)) = if S ⊆ onesSet z then 1 else 0 := by
  classical
  by_cases hS : S ⊆ onesSet z
  · rw [if_pos hS]
    refine Finset.prod_eq_one ?_
    intro j hj
    have : z j = 1 := (mem_onesSet_iff z j).mp (hS hj)
    simp [witnessPhi, this]
  · rw [if_neg hS]
    have : ∃ j ∈ S, z j ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hS fun j hj => (mem_onesSet_iff z j).mpr (hcon j hj)
    obtain ⟨j, hjS, hj⟩ := this
    refine Finset.prod_eq_zero hjS ?_
    simp [witnessPhi, hj]

/-- The cofactor as a function of the ones-set alone. -/
noncomputable def witnessCofactor (i : Fin 6) (N : Finset (Fin 6)) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin 6)).powerset,
    (if i ∈ S ∧ S.erase i ⊆ N then witnessW S else 0)

/-- The reduction: the cofactor at a context equals the cofactor at its
ones-set.  Every remaining numeric obligation about the interaction bound can be
stated over `Finset (Fin 6)` from here. -/
theorem multiaffineContextFactor_eq_witnessCofactor (i : Fin 6) (z : Fin 6 → Fin 3) :
    multiaffineContextFactor witnessPhi witnessW i z = witnessCofactor i (onesSet z) := by
  classical
  unfold multiaffineContextFactor witnessCofactor
  refine Finset.sum_congr rfl ?_
  intro S _
  by_cases hiS : i ∈ S
  · rw [if_pos hiS, witnessPhi_prod (S.erase i) z]
    by_cases hsub : S.erase i ⊆ onesSet z
    · rw [if_pos hsub, if_pos ⟨hiS, hsub⟩]
      ring
    · rw [if_neg hsub, if_neg (by tauto)]
      ring
  · rw [if_neg hiS, if_neg (by tauto)]

end CIGAMF.P13.D6StrictRankOneM6ContextFactor
