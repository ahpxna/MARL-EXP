import Mathlib

/-! A excluded upper endpoint may supply the infimum but is never silently
promoted to an admissible alternative. Nonempty domain is explicit. -/
namespace CIGAMF.P13.OpenQuadraticProfile
open Set
noncomputable section

theorem lower_bound_extends (f : ℝ → ℝ) (hf : Continuous f) (l U : ℝ) (hU : 0 < U)
    (hl : ∀ x ∈ Ico 0 U, l ≤ f x) : ∀ x ∈ Icc 0 U, l ≤ f x := by
  have hs : Ico 0 U ⊆ {x | l ≤ f x} := hl
  have hc := closure_minimal hs (isClosed_le continuous_const hf)
  rw [closure_Ico (ne_of_lt hU)] at hc
  exact hc

theorem half_open_inf_eq_minimum (f : ℝ → ℝ) (hf : Continuous f)
    (U p : ℝ) (hU : 0 < U) (hp : p ∈ Icc 0 U)
    (hmin : ∀ x ∈ Icc 0 U, f p ≤ f x) : sInf (f '' Ico 0 U) = f p := by
  have hn : (f '' Ico 0 U).Nonempty := ⟨f 0,0,⟨le_rfl,hU⟩,rfl⟩
  have hb : BddBelow (f '' Ico 0 U) := ⟨f p,by
    rintro _ ⟨x,hx,rfl⟩
    exact hmin x ⟨hx.1,hx.2.le⟩⟩
  apply le_antisymm
  · apply lower_bound_extends f hf _ U hU _ p hp
    intro x hx
    exact csInf_le hb ⟨x,hx,rfl⟩
  · apply le_csInf hn
    rintro _ ⟨x,hx,rfl⟩
    exact hmin x ⟨hx.1,hx.2.le⟩

def clipped (c b U : ℝ) : ℝ := max 0 (min U (b/c))

theorem quadratic_minimum (c b a U : ℝ) (hc : 0 < c) (hU : 0 ≤ U) :
    let p := clipped c b U
    p ∈ Icc 0 U ∧ ∀ x ∈ Icc 0 U,
      a-2*b*p+c*p^2 ≤ a-2*b*x+c*x^2 := by
  dsimp
  have hm : clipped c b U ∈ Icc 0 U := by
    unfold clipped
    exact ⟨le_max_left _ _,max_le hU (min_le_left _ _)⟩
  refine ⟨hm,?_⟩
  intro x hx
  unfold clipped
  by_cases hb : b/c ≤ 0
  · have hp : min U (b/c) ≤ 0 := (min_le_right _ _).trans hb
    rw [max_eq_left hp]
    have hb0 : b ≤ 0 := by have h := (div_le_iff₀ hc).mp hb; nlinarith
    nlinarith [mul_nonneg hc.le (sq_nonneg x),mul_nonpos_of_nonpos_of_nonneg hb0 hx.1]
  · have hb0 : 0 < b/c := lt_of_not_ge hb
    by_cases ht : U ≤ b/c
    · rw [min_eq_left ht,max_eq_right hU]
      have hbc : U*c ≤ b := (le_div_iff₀ hc).mp ht
      have hmul := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hbc)
      nlinarith [mul_nonneg hc.le (sq_nonneg (U-x))]
    · rw [min_eq_right (le_of_not_ge ht),max_eq_right hb0.le]
      have he : c*(b/c)=b := mul_div_cancel₀ b (ne_of_gt hc)
      nlinarith [mul_nonneg hc.le (sq_nonneg (x-b/c))]

#print axioms lower_bound_extends
#print axioms half_open_inf_eq_minimum
#print axioms quadratic_minimum
end
end CIGAMF.P13.OpenQuadraticProfile
