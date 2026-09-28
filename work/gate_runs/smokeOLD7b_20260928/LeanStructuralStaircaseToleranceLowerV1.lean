import «LeanStructuralStaircaseExactPrefixCoverV1»

/-! Matching-order tolerance obstruction: normalized staircase still needs r
rankings when epsilon<1/(2r). This is a family bound, not a fixed small witness. -/
namespace CIGAMF.P13.StructuralStaircaseToleranceLower
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralStaircaseFamily
open CIGAMF.P13.StructuralUnboundedPrefixCoverFamily
open CIGAMF.P13.StructuralStaircaseExactPrefixCover
noncomputable section

lemma osc_integer {Ω : Type*} [Fintype Ω] [Nonempty Ω] (g : Ω → ℝ)
    (hg : ∀ x, ∃ z : ℤ, g x=z) : ∃ z : ℤ, osc g=z := by
  obtain ⟨a,ha⟩ := exists_eq_maxVal g
  obtain ⟨b,hb⟩ := exists_eq_minVal g
  obtain ⟨u,hu⟩ := hg a
  obtain ⟨v,hv⟩ := hg b
  refine ⟨u-v,?_⟩
  simp only [osc,← ha,← hb,hu,hv,Int.cast_sub]

lemma component_integer {r : ℕ} (j : StairRel r) (a : StairAction r) :
    ∃ z : ℤ, staircaseF j a=z := by
  rcases j with ⟨i,b⟩
  cases a with
  | none => exact ⟨0,by simp [staircaseF]⟩
  | some a =>
    cases b
    · by_cases h : i=a
      · exact ⟨1,by simp [staircaseF,h]⟩
      · exact ⟨0,by simp [staircaseF,h]⟩
    · by_cases h : a ≤ i
      · exact ⟨-1,by simp [staircaseF,h]⟩
      · exact ⟨0,by simp [staircaseF,h]⟩

lemma twice_radius_integer {r : ℕ} (S : Finset (StairRel r)) :
    ∃ z : ℤ, 2*selectedRadius staircaseF S=z := by
  have hg : ∀ a, ∃ z : ℤ, sumComponent Sᶜ staircaseF a=z := by
    intro a
    choose z hz using (fun j : StairRel r => component_integer j a)
    refine ⟨∑ j ∈ Sᶜ,z j,?_⟩
    simp [sumComponent,hz]
  obtain ⟨z,hz⟩ := osc_integer _ hg
  refine ⟨z,?_⟩
  unfold selectedRadius supportOsc
  linarith

lemma normalized_epsilon_exact {r : ℕ} (hr : 0 < r) (eps : ℝ)
    (heps : 2*(r:ℝ)*eps < 1) (k : ℕ) (S : Finset (StairRel r))
    (ho : EpsilonOptimalAt (fun T => selectedRadius staircaseF T/(r:ℝ)) eps k S) :
    EpsilonOptimalAt (selectedRadius staircaseF) 0 k S := by
  refine ⟨ho.1,?_⟩
  intro T hT
  have h := ho.2 T hT
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have h' := (div_le_iff₀ hr').mp h
  have he : (selectedRadius staircaseF T/(r:ℝ)+eps)*(r:ℝ)=
      selectedRadius staircaseF T+eps*r := by field_simp
  rw [he] at h'
  obtain ⟨z,hz⟩ := twice_radius_integer S
  obtain ⟨w,hw⟩ := twice_radius_integer T
  have hzlt : (z:ℝ) < (w:ℝ)+1 := by nlinarith
  have hzint : z < w+1 := by exact_mod_cast hzlt
  have hzle : (z:ℝ) ≤ w := by exact_mod_cast (show z ≤ w by omega)
  linarith

/-- Since each component has oscillation one and there are 2r components,
dividing radius by r is exactly normalization by total component radius. -/
theorem normalized_tolerance_lower {r : ℕ} (hr : 0 < r) (eps : ℝ)
    (heps : 2*(r:ℝ)*eps < 1) :
    ¬ PrefixCoverDimensionAtMost
      (fun S => selectedRadius (staircaseF (r := r)) S/(r:ℝ)) eps (r-1) := by
  rintro ⟨menu,hcard,hcover⟩
  apply STRUCT_UNBOUNDED_staircase_prefix_dimension_ge hr
  refine ⟨menu,hcard,hcover.1,hcover.2.1,?_⟩
  intro k hk
  obtain ⟨rnk,hm,ho⟩ := hcover.2.2 k hk
  exact ⟨rnk,hm,normalized_epsilon_exact hr eps heps k _ ho⟩

theorem normalization (r : ℕ) (hr : 0 < r) :
    (∑ j : StairRel r,osc (staircaseF j)/2)=(r:ℝ) := by
  simp_rw [staircase_component_osc_one]
  simp [StairRel]

#print axioms twice_radius_integer
#print axioms normalized_tolerance_lower
#print axioms normalization
end
end CIGAMF.P13.StructuralStaircaseToleranceLower
