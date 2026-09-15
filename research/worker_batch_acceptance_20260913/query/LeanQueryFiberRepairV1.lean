import «LeanQuerySufficiencyQuantitativeV1»

/-! Scalar absolute-error repair on a finite population. No statistical
held-out generalization or novelty relative to test cover is asserted. -/
namespace CIGAMF.P13.QueryFiberRepair
open Finset
open CIGAMF.V7.QuerySufficiencyQuantitative
noncomputable section
variable {Θ Y : Type*} [Fintype Θ] [Nonempty Θ] [DecidableEq Y]
attribute [local instance] Classical.propDecidable

def fiber (R : Θ → Y) (y : Y) : Finset Θ := univ.filter (fun x => R x=y)
def values (R : Θ → Y) (g : Θ → ℝ) (y : Y) := (fiber R y).image g

def midpoint (R : Θ → Y) (g : Θ → ℝ) (y : Y) : ℝ :=
  if h : (values R g y).Nonempty then ((values R g y).max' h+(values R g y).min' h)/2 else 0

lemma values_member (R : Θ → Y) (g : Θ → ℝ) (x : Θ) : g x ∈ values R g (R x) := by
  exact mem_image.mpr ⟨x,by simp [fiber],rfl⟩

/-- The midpoint decoder supplies the constructive half of the fibre bound. -/
theorem midpoint_error (R : Θ → Y) (g : Θ → ℝ) (eps : ℝ)
    (hdiam : ∀ x x',R x=R x' → |g x-g x'| ≤ 2*eps) (x : Θ) :
    |midpoint R g (R x)-g x| ≤ eps := by
  have hv := values_member R g x
  have hn : (values R g (R x)).Nonempty := ⟨_,hv⟩
  obtain ⟨hi,hhi,hgHi⟩ := mem_image.mp (max'_mem (values R g (R x)) hn)
  obtain ⟨lo,hlo,hgLo⟩ := mem_image.mp (min'_mem (values R g (R x)) hn)
  have hs : R hi=R lo := by simpa [fiber] using (mem_filter.mp hhi).2.trans (mem_filter.mp hlo).2.symm
  have hgap := hdiam hi lo hs
  rw [hgHi,hgLo] at hgap
  have hup := le_max' (values R g (R x)) (g x) hv
  have hlow := min'_le (values R g (R x)) (g x) hv
  unfold midpoint
  rw [dif_pos hn]
  apply abs_le.mpr
  have h := le_trans (le_abs_self _) hgap
  constructor <;> linarith

/-- Exact feasibility criterion, including singleton and constant-target fibres. -/
theorem decoder_exists_iff_diameter (R : Θ → Y) (g : Θ → ℝ) (eps : ℝ) :
    (∃ psi : Y → ℝ,∀ x,|psi (R x)-g x| ≤ eps) ↔
      ∀ x x',R x=R x' → |g x-g x'| ≤ 2*eps := by
  constructor
  · rintro ⟨psi,hp⟩ x x' hR
    have h := E5_response_only_minimax_lower_bound R g psi x x' hR
    have hm : max |psi (R x)-g x| |psi (R x')-g x'| ≤ eps := max_le (hp x) (hp x')
    linarith
  · intro h
    exact ⟨midpoint R g,midpoint_error R g eps h⟩

/-- Feature selection repairs exactly the pairs beyond the allowed error. -/
theorem repair_iff_separates {L Z : Type*} [DecidableEq Z]
    (R : Θ → Y) (g : Θ → ℝ) (feature : L → Θ → Z) (J : Finset L) (eps : ℝ)
    (heps : 0 ≤ eps) :
    (∃ psi : (Y × (J → Z)) → ℝ,∀ x,
      |psi (R x,fun l => feature l.val x)-g x| ≤ eps) ↔
      ∀ x x',R x=R x' → 2*eps < |g x-g x'| → ∃ l ∈ J,feature l x ≠ feature l x' := by
  classical
  rw [decoder_exists_iff_diameter]
  constructor
  · intro h x x' hR hbad
    by_contra hnone
    have he : (fun l : J => feature l.val x)=(fun l : J => feature l.val x') := by
      funext l
      by_contra hn
      exact hnone ⟨l.val,l.property,hn⟩
    have hp := h x x' (Prod.ext hR he)
    linarith
  · intro h x x' he
    by_contra hbad
    obtain ⟨l,hl,hn⟩ := h x x' (congrArg Prod.fst he) (by linarith)
    have hp := congrArg (fun p : Y × (J → Z) => p.2 ⟨l,hl⟩) he
    exact hn hp

#print axioms midpoint_error
#print axioms decoder_exists_iff_diameter
#print axioms repair_iff_separates
end
end CIGAMF.P13.QueryFiberRepair
