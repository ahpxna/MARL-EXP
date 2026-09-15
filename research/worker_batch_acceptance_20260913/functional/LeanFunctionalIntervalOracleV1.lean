import «LeanFunctionalExtremaSeparationV1»

/-! Exact shrink and pair-opening ingredients for the full-extrema oracle.
All cells are free coordinates. No shared-F coupling or allocator advantage
is asserted. The global infimum decomposition is a separate result. -/
namespace CIGAMF.P13.FunctionalIntervalOracle
open scoped BigOperators
open Finset
open CIGAMF.P13.FunctionalExtremaSeparation
noncomputable section

def project (ell z x : ℝ) := min (ell+z) (max ell x)

lemma project_mem (ell z x : ℝ) (hz : 0 ≤ z) : ell ≤ project ell z x ∧ project ell z x ≤ ell+z := by
  unfold project
  constructor
  · exact le_min (by linarith) (le_max_left _ _)
  · exact min_le_left _ _

/-- Interval projection solves each weighted cell problem, including zero weight. -/
theorem projection_interval_min (ell z theta y p : ℝ) (hz : 0 ≤ z) (hp : 0 ≤ p)
    (hy0 : ell ≤ y) (hy1 : y ≤ ell+z) :
    p*(project ell z theta-theta)^2 ≤ p*(y-theta)^2 := by
  apply mul_le_mul_of_nonneg_left _ hp
  by_cases hl : theta ≤ ell
  · have he : project ell z theta=ell := by simp [project,max_eq_left hl,min_eq_right (by linarith : ell ≤ ell+z)]
    rw [he]
    nlinarith
  · by_cases hu : theta ≤ ell+z
    · have he : project ell z theta=theta := by simp [project,max_eq_right (by linarith : ell ≤ theta),min_eq_right hu]
      rw [he]
      nlinarith [sq_nonneg (y-theta)]
    · have he : project ell z theta=ell+z := by simp [project,max_eq_right (by linarith : ell ≤ theta),min_eq_left (by linarith : ell+z ≤ theta)]
      rw [he]
      nlinarith

theorem range_le_iff_interval (v : Row) (z : ℝ) :
    capacity v ≤ z ↔ ∃ ell,∀ a,ell ≤ v a ∧ v a ≤ ell+z := by
  constructor
  · intro h
    refine ⟨low v,fun a => ⟨low_le v a,?_⟩⟩
    have := le_high v a
    unfold capacity at h
    linarith
  · rintro ⟨ell,h⟩
    obtain ⟨a,ha⟩ := high_mem v
    obtain ⟨b,hb⟩ := low_mem v
    unfold capacity
    rw [ha,hb]
    linarith [(h a).2,(h b).1]

theorem range_ge_iff_pair (v : Row) (z : ℝ) (hz : 0 ≤ z) :
    z ≤ capacity v ↔ ∃ a b : Fin 3,a ≠ b ∧ z ≤ v a-v b := by
  constructor
  · intro h
    by_cases h0 : capacity v=0
    · have hz0 : z=0 := by linarith
      have he : v 0=v 1 := by
        have h1 := pair_le_capacity v 0 1
        have h2 := pair_le_capacity v 1 0
        rw [h0] at h1 h2
        linarith
      exact ⟨0,1,by decide,by rw [hz0,he];simp⟩
    · obtain ⟨a,ha⟩ := high_mem v
      obtain ⟨b,hb⟩ := low_mem v
      refine ⟨a,b,?_,?_⟩
      · intro he
        apply h0
        simp [capacity,ha,hb,he]
      · simpa [capacity,ha,hb] using h
  · rintro ⟨a,b,_,h⟩
    exact h.trans (pair_le_capacity v a b)

/-- Summed projection inequality for the complete relation block. -/
theorem shrink_projection (p theta v : Row) (ell z : ℝ) (hz : 0 ≤ z)
    (hp : ∀ a,0 ≤ p a) (hv : ∀ a,ell ≤ v a ∧ v a ≤ ell+z) :
    capacity (fun a => project ell z (theta a)) ≤ z ∧
      rowEnergy p theta (fun a => project ell z (theta a)) ≤ rowEnergy p theta v := by
  constructor
  · exact (range_le_iff_interval _ _).mpr ⟨ell,fun a => project_mem ell z (theta a) hz⟩
  · unfold rowEnergy
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact sum_le_sum (fun a _ => projection_interval_min ell z (theta a) (v a) (p a) hz (hp a) (hv a).1 (hv a).2)

def pairEnergy (p q x y : ℝ) := (p*x^2+q*y^2)/2
def openingCost (p q gap : ℝ) := p*q*(max 0 gap)^2/(2*(p+q))

lemma pair_decomposition (p q x y : ℝ) (hp : 0 < p) (hq : 0 < q) :
    pairEnergy p q x y=p*q*(x-y)^2/(2*(p+q))+(p*x+q*y)^2/(2*(p+q)) := by
  unfold pairEnergy
  field_simp
  <;> ring

theorem pair_open_lower (p q gap x y : ℝ) (hp : 0 < p) (hq : 0 < q) (hg : gap ≤ x-y) :
    openingCost p q gap ≤ pairEnergy p q x y := by
  by_cases hgap : 0 ≤ gap
  · unfold openingCost
    rw [max_eq_right hgap,pair_decomposition p q x y hp hq]
    have hsq : gap^2 ≤ (x-y)^2 := by nlinarith
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ p*q))
      (by positivity : 0 ≤ 2*(p+q))
    have hh : 0 ≤ (p*x+q*y)^2/(2*(p+q)) := by positivity
    linarith
  · unfold openingCost pairEnergy
    rw [max_eq_left (by linarith)]
    simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,zero_div]
    positivity

/-- The explicit displacement realizes the boundary; no optimizer is assumed. -/
theorem pair_open_attained (p q gap : ℝ) (hp : 0 < p) (hq : 0 < q) :
    let x := max 0 gap*q/(p+q)
    let y := -(max 0 gap)*p/(p+q)
    gap ≤ x-y ∧ pairEnergy p q x y=openingCost p q gap := by
  dsimp only
  have hsum : p+q ≠ 0 := by positivity
  have hid : max 0 gap*q/(p+q)-(-(max 0 gap)*p/(p+q))=max 0 gap := by field_simp;ring
  constructor
  · rw [hid]
    exact le_max_right _ _
  · unfold pairEnergy openingCost
    field_simp
    <;> ring

theorem reciprocal_cost_formula (p q gap : ℝ) (hp : 0 < p) (hq : 0 < q) :
    openingCost p q gap=(max 0 gap)^2/(2*(1/p+1/q)) := by
  unfold openingCost
  field_simp
  <;> ring

#print axioms projection_interval_min
#print axioms range_le_iff_interval
#print axioms range_ge_iff_pair
#print axioms shrink_projection
#print axioms pair_open_lower
#print axioms pair_open_attained
#print axioms reciprocal_cost_formula
end
end CIGAMF.P13.FunctionalIntervalOracle
