import «LeanD6AllocationPhaseThreeFeasibleV1»

/-! The two-sided boundary regime is nonempty for every q >= 3. This prevents
local matching statements from relying on a possibly empty phase interval. -/
namespace CIGAMF.P13.D6BoundaryNondegenerate
open CIGAMF.P13.D6ExpandedAllocation CIGAMF.P13.D6AllocationMarginRegion
open CIGAMF.P13.D6AllocationPhaseThreeFeasible CIGAMF.P13.D6AllocationMargin
noncomputable section

lemma radius_square_identity (q : ℝ) (hq : 3 ≤ q) :
    (q+1)*(radius q)^2=q^2+2*q^2*tilt q+(tilt q)^2 := by
  have h := radius_balance q hq
  unfold gain at h
  nlinarith only [h]

/-- Strict phase-II / phase-III boundary placement, for the entire D6 family. -/
theorem boundary_strict_interval (q : ℝ) (hq : 3 ≤ q) :
    marginMin q < 1/2 ∧ 1/2 < marginMax q ∧ marginMax q < marginHigh q ∧ marginHigh q < 1 := by
  have hc := scale_properties q hq
  have hz := root_properties q (scale q) hq hc.1 hc.2.1 hc.2.2
  have hz0 : 0 < tilt q := tilt_pos q hq
  have hzb : 4*q*tilt q ≤ 1 := hz.2.1
  have hz1 : tilt q ≤ 1 := by nlinarith
  have hr0 := radius_pos q hq
  have hr := radius_square_identity q hq
  have hr1 : 1 < radius q := by
    have hpos : 0 ≤ 2*q^2*tilt q := by positivity
    have hqpos : 0 ≤ (q-3)*(q+2) := mul_nonneg (by linarith) (by linarith)
    have hq1 : 0 < q+1 := by linarith
    have hrsq : 1 < (radius q)^2 := by
      apply (mul_lt_mul_iff_right₀ hq1).mp
      nlinarith only [hr,hpos,hqpos,sq_nonneg (tilt q)]
    nlinarith only [hrsq,hr0]
  have hmul := mul_le_mul_of_nonneg_left hzb (show 0 ≤ q by linarith)
  have hrq : (radius q)^2 < q := by nlinarith [sq_nonneg (1-tilt q)]
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have hs2 := Real.sq_sqrt (show 0 ≤ q by linarith)
  have hrr : radius q < Real.sqrt q := by nlinarith
  have hd : 0 < 1+radius q := by linarith
  have hds : 0 < 1+Real.sqrt q := by linarith
  refine ⟨?_,?_,?_,?_⟩
  · unfold marginMin
    apply (div_lt_iff₀ (show 0 < q-1 by linarith)).mpr
    linarith [hc.1]
  · unfold marginMax
    apply (lt_div_iff₀ hd).mpr
    linarith
  · unfold marginMax marginHigh
    apply (div_lt_div_iff₀ hd hds).mpr
    nlinarith only [hrr]
  · unfold marginHigh
    apply (div_lt_one hds).mpr
    linarith

theorem boundary_interior (q : ℝ) (hq : 3 ≤ q) : Interior q (1-marginMax q) := by
  have h := boundary_strict_interval q hq
  apply (interior_iff_margin q (marginMax q) hq).mpr
  exact ⟨by linarith,rfl.le⟩

/-- A positive explicit neighborhood has a phase-II minus point and phase-III
plus point, with the scalar-design feasibility interval respected. -/
theorem positive_two_sided_neighborhood (q : ℝ) (hq : 3 ≤ q) :
    ∃ eta : ℝ,0 < eta ∧ ∀ eps : ℝ,0 ≤ eps → eps ≤ eta →
      Interior q (1-(marginMax q-eps)) ∧ 1/2 ≤ marginMax q-eps ∧
      marginMax q+eps ≤ marginHigh q := by
  have h := boundary_strict_interval q hq
  let eta := min (marginMax q-1/2) (marginHigh q-marginMax q)
  have he : 0 < eta := lt_min (by linarith) (by linarith)
  refine ⟨eta,he,?_⟩
  intro eps hp hbound
  have he1 := hbound.trans (min_le_left _ _)
  have he2 := hbound.trans (min_le_right _ _)
  refine ⟨?_,by linarith,by linarith⟩
  apply (interior_iff_margin q (marginMax q-eps) hq).mpr
  exact ⟨by linarith,by linarith⟩

#print axioms boundary_strict_interval
#print axioms boundary_interior
#print axioms positive_two_sided_neighborhood
end
end CIGAMF.P13.D6BoundaryNondegenerate
