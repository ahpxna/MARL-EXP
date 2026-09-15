import «LeanD6BoundaryNondegenerateV1»

/-! Positive neighborhood satisfying every phase and co-moving nuisance
condition in the local matching theorem, for all q >= 3. -/
namespace CIGAMF.P13.D6MatchingNeighborhood
open CIGAMF.P13.D6BoundaryNondegenerate CIGAMF.P13.D6ExpandedAllocation
open CIGAMF.P13.D6AllocationMarginRegion CIGAMF.P13.D6AllocationMargin
open CIGAMF.P13.D6AllocationPhaseThreeFeasible
noncomputable section

theorem boundary_nuisance_strict (q : ℝ) (hq : 3 ≤ q) :
    0 < (1-marginMax q)*(1+root q (scale q)) ∧
      (1-marginMax q)*(1+root q (scale q)) < 1 := by
  have h := boundary_strict_interval q hq
  have hc := scale_properties q hq
  have hz := root_properties q (scale q) hq hc.1 hc.2.1 hc.2.2
  have hz1 : root q (scale q) < 1 := by nlinarith [hz.1,hz.2.1]
  have hm1 : marginMax q < 1 := h.2.2.1.trans h.2.2.2
  constructor
  · exact mul_pos (by linarith) (by linarith [hz.1])
  · have hmul := mul_lt_mul_of_pos_left hz1 (show 0 < 1-marginMax q by linarith)
    nlinarith only [hmul,h.2.1]

/-- All feasibility premises of both matching bounds hold on one positive
interval. No unknown nuisance feasibility remains as an extra assumption. -/
theorem matching_neighborhood (q : ℝ) (hq : 3 ≤ q) :
    ∃ eta : ℝ,0 < eta ∧ ∀ eps : ℝ,0 ≤ eps → eps ≤ eta →
      Interior q (1-marginMax q) ∧
      Interior q (1-(marginMax q-eps)) ∧
      1/2 ≤ marginMax q-eps ∧ marginMax q+eps ≤ marginHigh q ∧
      eps ≤ 1-(1-marginMax q)*(1+root q (scale q)) ∧
      eps ≤ (1-marginMax q)*(1+root q (scale q)) := by
  obtain ⟨eta,he,hlocal⟩ := positive_two_sided_neighborhood q hq
  have hn := boundary_nuisance_strict q hq
  refine ⟨min eta (min (1-(1-marginMax q)*(1+root q (scale q)))
    ((1-marginMax q)*(1+root q (scale q)))),
    lt_min he (lt_min (by linarith) hn.1),?_⟩
  intro eps hp hb
  have heps := hb.trans (min_le_left _ _)
  have hnu := hb.trans (min_le_right _ _)
  have hphase := hlocal eps hp heps
  exact ⟨boundary_interior q hq,hphase.1,hphase.2.1,hphase.2.2,
    hnu.trans (min_le_left _ _),hnu.trans (min_le_right _ _)⟩

#print axioms boundary_nuisance_strict
#print axioms matching_neighborhood
end
end CIGAMF.P13.D6MatchingNeighborhood
