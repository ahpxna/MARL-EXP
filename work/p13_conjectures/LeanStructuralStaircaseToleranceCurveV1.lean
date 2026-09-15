import «LeanStructuralStaircaseToleranceLowerV1»
import «LeanStructuralStaircaseApproximationV1»

/-! The complete normalized tolerance curve of every staircase instance.
Both branches follow from actual support-radius constructions. This closes
the finite-family curve observed numerically without extrapolating from small r. -/
namespace CIGAMF.P13.StructuralStaircaseToleranceCurve
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralMinimumTransversalWidth
open CIGAMF.P13.StructuralStaircaseFamily
open CIGAMF.P13.StructuralStaircaseExactPrefixCover
open CIGAMF.P13.StructuralStaircaseToleranceLower
open CIGAMF.P13.StructuralStaircaseApproximation
noncomputable section

lemma normalized_cover_r {r : ℕ} (hr : 0 < r) (eps : ℝ) (heps : 0 ≤ eps) :
    PrefixCoverDimensionAtMost
      (fun S => selectedRadius (@staircaseF r) S/(r:ℝ)) eps r := by
  obtain ⟨menu,hcard,hne,hfull,hcover⟩ := STRUCT_staircase_prefix_cover_at_most_r hr
  refine ⟨menu,hcard,hne,hfull,?_⟩
  intro k hk
  obtain ⟨ranking,hm,ho⟩ := hcover k hk
  refine ⟨ranking,hm,ho.1,?_⟩
  intro T hT
  have hh := div_le_div_of_nonneg_right (ho.2 T hT) (by positivity : (0:ℝ) ≤ r)
  simp only [add_zero] at hh
  linarith

/-- Every positive-r staircase has exactly r required rankings below the
threshold, including arbitrarily close to it. -/
theorem dimension_below {r : ℕ} (hr : 0 < r) (eps : ℝ) (heps : 0 ≤ eps)
    (hlt : eps < 1/(2*(r:ℝ))) :
    prefixDimensionValue (fun S => selectedRadius (@staircaseF r) S/(r:ℝ)) eps=r := by
  let R : Finset (StairRel r) → ℝ := fun S => selectedRadius staircaseF S/(r:ℝ)
  have hu : PrefixCoverDimensionAtMost R eps r := normalized_cover_r hr eps heps
  have hf : {K : ℕ | PrefixCoverDimensionAtMost R eps K}.Nonempty := ⟨r,hu⟩
  have ht : 2*(r:ℝ)*eps < 1 := by
    have hh := (lt_div_iff₀ (by positivity : (0:ℝ)<2*r)).mp hlt
    nlinarith
  apply le_antisymm (Nat.sInf_le hu)
  by_contra h
  have hs : prefixDimensionValue R eps ≤ r-1 := by
    change ¬ r ≤ prefixDimensionValue R eps at h
    omega
  obtain ⟨menu,hcard,hcover⟩ := (Nat.sInf_mem hf : PrefixCoverDimensionAtMost R eps (prefixDimensionValue R eps))
  exact normalized_tolerance_lower hr eps ht ⟨menu,hcard.trans hs,hcover⟩

/-- At the threshold itself the negative-first ranking already suffices. -/
theorem dimension_above {r : ℕ} (hr : 0 < r) (eps : ℝ)
    (hle : 1/(2*(r:ℝ)) ≤ eps) :
    prefixDimensionValue (fun S => selectedRadius (@staircaseF r) S/(r:ℝ)) eps=1 := by
  let R : Finset (StairRel r) → ℝ := fun S => selectedRadius staircaseF S/(r:ℝ)
  obtain ⟨ranking,hcover⟩ :=
    (singleton_prefix_cover_iff_one_prefix_chain R (1/(2*(r:ℝ)))).mpr (one_ranking_normalized r hr)
  have hu : PrefixCoverDimensionAtMost R eps 1 :=
    STRUCT_B3_tolerance_monotonicity R _ eps hle 1 ⟨{ranking},by simp,hcover⟩
  have hf : {K : ℕ | PrefixCoverDimensionAtMost R eps K}.Nonempty := ⟨1,hu⟩
  apply le_antisymm (Nat.sInf_le hu)
  obtain ⟨menu,hcard,hcover⟩ := (Nat.sInf_mem hf : PrefixCoverDimensionAtMost R eps (prefixDimensionValue R eps))
  exact (card_pos.mpr hcover.1).trans_le hcard

/-- Complete curve, for all r>0 and all nonnegative normalized tolerances.
For r=1 both values coincide, so there is no strict jump in that edge case. -/
theorem exact_curve {r : ℕ} (hr : 0 < r) (eps : ℝ) (heps : 0 ≤ eps) :
    prefixDimensionValue (fun S => selectedRadius (@staircaseF r) S/(r:ℝ)) eps =
      if eps < 1/(2*(r:ℝ)) then r else 1 := by
  split
  · exact dimension_below hr eps heps ‹_›
  · exact dimension_above hr eps (le_of_not_gt ‹_›)

#print axioms normalized_cover_r
#print axioms dimension_below
#print axioms dimension_above
#print axioms exact_curve
end
end CIGAMF.P13.StructuralStaircaseToleranceCurve
