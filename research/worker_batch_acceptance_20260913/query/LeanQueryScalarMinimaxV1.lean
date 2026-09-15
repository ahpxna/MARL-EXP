import «LeanQueryFiberRepairV1»

/-! Exact scalar minimax radius on a finite population, including zero radius. -/
namespace CIGAMF.P13.QueryScalarMinimax
open Finset CIGAMF.P13.QueryFiberRepair
noncomputable section
variable {Θ Y : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Y]
attribute [local instance] Classical.propDecidable

def pairDistances (R : Θ → Y) (g : Θ → ℝ) : Finset ℝ :=
  (univ.filter (fun p : Θ × Θ => R p.1=R p.2)).image (fun p => |g p.1-g p.2|)

lemma pairDistances_nonempty (R : Θ → Y) (g : Θ → ℝ) : (pairDistances R g).Nonempty := by
  let x : Θ := Classical.choice inferInstance
  exact ⟨0,mem_image.mpr ⟨(x,x),by simp,by simp⟩⟩

def radius (R : Θ → Y) (g : Θ → ℝ) : ℝ :=
  (pairDistances R g).max' (pairDistances_nonempty R g)/2

lemma radius_nonneg (R : Θ → Y) (g : Θ → ℝ) : 0 ≤ radius R g := by
  obtain ⟨p,hp,he⟩ := mem_image.mp (max'_mem _ (pairDistances_nonempty R g))
  unfold radius
  rw [← he]
  positivity

/-- This is the maximum diameter over all nonempty representation fibres. -/
theorem diameter_iff_radius (R : Θ → Y) (g : Θ → ℝ) (eps : ℝ) :
    (∀ x x',R x=R x' → |g x-g x'| ≤ 2*eps) ↔ radius R g ≤ eps := by
  unfold radius
  rw [div_le_iff₀ (by norm_num : (0:ℝ)<2)]
  constructor
  · intro h
    obtain ⟨p,hp,he⟩ := mem_image.mp (max'_mem _ (pairDistances_nonempty R g))
    rw [← he]
    have := h p.1 p.2 (mem_filter.mp hp).2
    linarith
  · intro h x x' he
    have hm : |g x-g x'| ∈ pairDistances R g := mem_image.mpr ⟨(x,x'),by simp [he],rfl⟩
    have hl := le_max' _ _ hm
    linarith

/-- The explicit midpoint attains the exact minimax radius. -/
theorem midpoint_optimal (R : Θ → Y) (g : Θ → ℝ) :
    (∀ x,|midpoint R g (R x)-g x| ≤ radius R g) ∧
    (∀ psi : Y → ℝ,∃ x,radius R g ≤ |psi (R x)-g x|) := by
  refine ⟨midpoint_error R g _ ((diameter_iff_radius R g _).mpr le_rfl),?_⟩
  intro psi
  obtain ⟨p,hp,he⟩ := mem_image.mp (max'_mem _ (pairDistances_nonempty R g))
  have h := CIGAMF.V7.QuerySufficiencyQuantitative.E5_response_only_minimax_lower_bound R g psi p.1 p.2 (mem_filter.mp hp).2
  have hr : radius R g=|g p.1-g p.2|/2 := by unfold radius;rw [← he]
  rw [hr]
  rcases le_total |psi (R p.1)-g p.1| |psi (R p.2)-g p.2| with hh | hh
  · exact ⟨p.2,by simpa only [max_eq_right hh] using h⟩
  · exact ⟨p.1,by simpa only [max_eq_left hh] using h⟩

def feasibleErrors (R : Θ → Y) (g : Θ → ℝ) : Set ℝ :=
  {eps | ∃ psi : Y → ℝ,∀ x,|psi (R x)-g x| ≤ eps}

/-- No externally assumed optimizer or restriction to nonconstant targets. -/
theorem minimax_radius (R : Θ → Y) (g : Θ → ℝ) :
    sInf (feasibleErrors R g)=radius R g := by
  have hm : radius R g ∈ feasibleErrors R g := ⟨midpoint R g,(midpoint_optimal R g).1⟩
  have hl : ∀ eps ∈ feasibleErrors R g,radius R g ≤ eps := by
    intro eps he
    exact (diameter_iff_radius R g eps).mp ((decoder_exists_iff_diameter R g eps).mp he)
  exact le_antisymm (csInf_le ⟨radius R g,hl⟩ hm) (le_csInf ⟨_,hm⟩ hl)

#print axioms radius_nonneg
#print axioms diameter_iff_radius
#print axioms midpoint_optimal
#print axioms minimax_radius
end
end CIGAMF.P13.QueryScalarMinimax
