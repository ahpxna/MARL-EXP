import Mathlib
import «LeanD6StrictRankOneM6WitnessV1»

/-!
# Response spans of the m = 6 strict witness

At a CORNER (point-mass) product reference the product response collapses to a
single slice value:

  `productResponse cornerQ6 F i u = F (update (fun _ => 0) i u)`

so the response table is 18 numbers, not a sum over 729 actions.  That is the
whole reason the corner reference is worth using here: the response layer costs
nothing, and only the loss and mixed-difference layers see the full grid.

Proved here: the 18 response values, and the six spans

  `C = (23, 23, 23, 22, 22, 22)`.

No decision bound is claimed.  Nothing here is `sorry`ed.
-/

namespace CIGAMF.P13.D6StrictRankOneM6ResponseSpans

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ScalarMultiaffineRankOne
open CIGAMF.P13.D6StrictRankOneM6Witness

/-- The corner reference puts all its mass on the all-zero action. -/
theorem cornerQ6_jointWeight (c : Fin 6 → Fin 3) :
    jointWeight cornerQ6 c = if c = (fun _ => 0) then 1 else 0 := by
  classical
  unfold jointWeight cornerQ6
  by_cases h : c = (fun _ => 0)
  · subst h
    simp
  · have : ∃ j, c j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact h (funext fun j => hcon j)
    obtain ⟨j, hj⟩ := this
    rw [if_neg h]
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    simp [hj]

/-- At a point-mass reference the product response is one slice value. -/
theorem productResponse_cornerQ6 (F : (Fin 6 → Fin 3) → ℝ) (i : Fin 6) (u : Fin 3) :
    productResponse cornerQ6 F i u = F (Function.update (fun _ => 0) i u) := by
  classical
  unfold productResponse productExpectation
  rw [Finset.sum_congr rfl (fun c _ => by
    rw [cornerQ6_jointWeight c])]
  simp

private theorem additive_at_corner_slice (i : Fin 6) (u : Fin 3) :
    (∑ j, witnessG j ((Function.update (fun _ => (0 : Fin 3)) i u) j)) = witnessG i u := by
  classical
  rw [Finset.sum_eq_single i]
  · simp [Function.update]
  · intro j _ hji
    simp [Function.update, hji, witnessG]
  · simp

private theorem core_zero_at_corner_slice (i : Fin 6) (u : Fin 3) :
    (∑ S ∈ (Finset.univ : Finset (Fin 6)).powerset,
      witnessW S *
        ∏ j ∈ S, witnessPhi j ((Function.update (fun _ => (0 : Fin 3)) i u) j)) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro S _
  by_cases hS : S ⊆ ({i} : Finset (Fin 6))
  · -- only the empty set and the singleton survive, and the core vanishes on both
    rcases Finset.subset_singleton_iff.mp hS with h | h
    · subst h
      simp [witnessW, subsetMask, witnessCore, witnessCoreQ]
    · subst h
      have : witnessW ({i} : Finset (Fin 6)) = 0 := by
        unfold witnessW subsetMask
        fin_cases i <;> simp [witnessCore, witnessCoreQ]
      rw [this]
      ring
  · -- some coordinate other than i is present, and phi vanishes there
    have : ∃ j ∈ S, j ≠ i := by
      by_contra hcon
      push_neg at hcon
      exact hS fun j hj => Finset.mem_singleton.mpr (hcon j hj)
    obtain ⟨j, hjS, hji⟩ := this
    have hzero : ∏ j' ∈ S,
        witnessPhi j' ((Function.update (fun _ => (0 : Fin 3)) i u) j') = 0 := by
      refine Finset.prod_eq_zero hjS ?_
      simp [Function.update, hji, witnessPhi]
    rw [hzero]
    ring

/-- The witness at a corner slice is the constant plus one additive entry. -/
theorem witnessWorld_corner_slice (i : Fin 6) (u : Fin 3) :
    witnessWorld (Function.update (fun _ => 0) i u) = witnessB + witnessG i u := by
  unfold witnessWorld scalarMultiaffineWorld
  rw [additive_at_corner_slice i u, core_zero_at_corner_slice i u]
  ring

/-- The 18 response values, in closed form. -/
theorem witnessResponse_eq (i : Fin 6) (u : Fin 3) :
    productResponse cornerQ6 witnessWorld i u = -65 + witnessG i u := by
  rw [productResponse_cornerQ6 witnessWorld i u, witnessWorld_corner_slice i u]
  norm_num [witnessB]


/-- Oscillation of a three-point real function from explicit bounds and
attainment.  Reusable, and it keeps every span proof below to four short
obligations instead of unfolding `maxVal`/`minVal` six times. -/
private theorem osc_fin3 (f : Fin 3 → ℝ) (M m : ℝ)
    (hM : ∀ u, f u ≤ M) (hMe : ∃ u, f u = M)
    (hm : ∀ u, m ≤ f u) (hme : ∃ u, f u = m) :
    osc f = M - m := by
  have h1 : maxVal f = M := by
    refine le_antisymm (maxVal_le f hM) ?_
    obtain ⟨u, hu⟩ := hMe
    rw [← hu]
    exact le_maxVal f u
  have h2 : minVal f = m := by
    refine le_antisymm ?_ (le_minVal f hm)
    obtain ⟨u, hu⟩ := hme
    rw [← hu]
    exact minVal_le f u
  unfold osc
  rw [h1, h2]

theorem witnessResponse_span_zero :
    osc (productResponse cornerQ6 witnessWorld 0) = 23 := by
  have h : osc (productResponse cornerQ6 witnessWorld 0) = (-42) - (-65) := by
    refine osc_fin3 _ (-42) (-65) ?_ ⟨1, ?_⟩ ?_ ⟨0, ?_⟩
    · intro u; fin_cases u <;> norm_num [witnessResponse_eq, witnessG]
    · norm_num [witnessResponse_eq, witnessG]
    · intro u; fin_cases u <;> norm_num [witnessResponse_eq, witnessG]
    · norm_num [witnessResponse_eq, witnessG]
  rw [h]; norm_num

theorem witnessResponse_span_one :
    osc (productResponse cornerQ6 witnessWorld 1) = 23 := by
  have h : osc (productResponse cornerQ6 witnessWorld 1) = (-42) - (-65) := by
    refine osc_fin3 _ (-42) (-65) ?_ ⟨1, ?_⟩ ?_ ⟨0, ?_⟩
    · intro u; fin_cases u <;> norm_num [witnessResponse_eq, witnessG]
    · norm_num [witnessResponse_eq, witnessG]
    · intro u; fin_cases u <;> norm_num [witnessResponse_eq, witnessG]
    · norm_num [witnessResponse_eq, witnessG]
  rw [h]; norm_num

theorem witnessResponse_span_two :
    osc (productResponse cornerQ6 witnessWorld 2) = 23 := by
  have h : osc (productResponse cornerQ6 witnessWorld 2) = (-42) - (-65) := by
    refine osc_fin3 _ (-42) (-65) ?_ ⟨1, ?_⟩ ?_ ⟨0, ?_⟩
    · intro u; fin_cases u <;> norm_num [witnessResponse_eq, witnessG]
    · norm_num [witnessResponse_eq, witnessG]
    · intro u; fin_cases u <;> norm_num [witnessResponse_eq, witnessG]
    · norm_num [witnessResponse_eq, witnessG]
  rw [h]; norm_num

theorem witnessResponse_span_three :
    osc (productResponse cornerQ6 witnessWorld 3) = 22 := by
  have h : osc (productResponse cornerQ6 witnessWorld 3) = (-43) - (-65) := by
    refine osc_fin3 _ (-43) (-65) ?_ ⟨1, ?_⟩ ?_ ⟨0, ?_⟩
    · intro u; fin_cases u <;> norm_num [witnessResponse_eq, witnessG]
    · norm_num [witnessResponse_eq, witnessG]
    · intro u; fin_cases u <;> norm_num [witnessResponse_eq, witnessG]
    · norm_num [witnessResponse_eq, witnessG]
  rw [h]; norm_num

theorem witnessResponse_span_four :
    osc (productResponse cornerQ6 witnessWorld 4) = 22 := by
  have h : osc (productResponse cornerQ6 witnessWorld 4) = (-43) - (-65) := by
    refine osc_fin3 _ (-43) (-65) ?_ ⟨1, ?_⟩ ?_ ⟨0, ?_⟩
    · intro u; fin_cases u <;> norm_num [witnessResponse_eq, witnessG]
    · norm_num [witnessResponse_eq, witnessG]
    · intro u; fin_cases u <;> norm_num [witnessResponse_eq, witnessG]
    · norm_num [witnessResponse_eq, witnessG]
  rw [h]; norm_num

/-- Coordinate 5 is the one whose latent-inactive action carries the offset, so
its maximum sits at action `2` rather than action `1`. -/
theorem witnessResponse_span_five :
    osc (productResponse cornerQ6 witnessWorld 5) = 22 := by
  have h : osc (productResponse cornerQ6 witnessWorld 5) = (-43) - (-65) := by
    refine osc_fin3 _ (-43) (-65) ?_ ⟨2, ?_⟩ ?_ ⟨0, ?_⟩
    · intro u; fin_cases u <;> norm_num [witnessResponse_eq, witnessG]
    · norm_num [witnessResponse_eq, witnessG]
    · intro u; fin_cases u <;> norm_num [witnessResponse_eq, witnessG]
    · norm_num [witnessResponse_eq, witnessG]
  rw [h]; norm_num

/-- The response spans: `C = (23, 23, 23, 22, 22, 22)`.  The three selected
coordinates are STRICTLY above the three unselected ones, by exactly 1. -/
theorem witnessResponse_spans :
    osc (productResponse cornerQ6 witnessWorld 0) = 23 ∧
    osc (productResponse cornerQ6 witnessWorld 1) = 23 ∧
    osc (productResponse cornerQ6 witnessWorld 2) = 23 ∧
    osc (productResponse cornerQ6 witnessWorld 3) = 22 ∧
    osc (productResponse cornerQ6 witnessWorld 4) = 22 ∧
    osc (productResponse cornerQ6 witnessWorld 5) = 22 :=
  ⟨witnessResponse_span_zero, witnessResponse_span_one, witnessResponse_span_two,
   witnessResponse_span_three, witnessResponse_span_four, witnessResponse_span_five⟩

end CIGAMF.P13.D6StrictRankOneM6ResponseSpans
