import Mathlib

/-! Exact deterministic bounded-noise minimax on every finite nonempty world
family, retaining constant-target worlds. Coordinates have fixed physical units. -/
namespace CIGAMF.P13.QueryResolutionMinimax
open scoped BigOperators
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Θ D : Type*} [Fintype Θ] [Nonempty Θ]

def Compatible (R : Θ → D → ℝ) (eta : ℝ) (x : Θ) (y : D → ℝ) : Prop :=
  ∀ i, |y i-R x i| ≤ eta

def Close (R : Θ → D → ℝ) (eta : ℝ) (x z : Θ) : Prop :=
  ∀ i, |R x i-R z i| ≤ 2*eta

theorem balls_intersect_iff (R : Θ → D → ℝ) (eta : ℝ) (x z : Θ) :
    (∃ y, Compatible R eta x y ∧ Compatible R eta z y) ↔ Close R eta x z := by
  constructor
  · rintro ⟨y,hx,hz⟩ i
    have ht := abs_sub_le (R x i) (y i) (R z i)
    rw [abs_sub_comm (R x i) (y i)] at ht
    linarith [hx i,hz i]
  · intro h
    refine ⟨fun i => (R x i+R z i)/2,?_,?_⟩
    · intro i
      have hp := abs_le.mp (h i)
      apply abs_le.mpr
      constructor <;> linarith [hp.1,hp.2]
    · intro i
      have hp := abs_le.mp (h i)
      apply abs_le.mpr
      constructor <;> linarith [hp.1,hp.2]

def pairDistances (R : Θ → D → ℝ) (g : Θ → ℝ) (eta : ℝ) : Finset ℝ :=
  (univ.filter (fun p : Θ × Θ => Close R eta p.1 p.2)).image (fun p => |g p.1-g p.2|)

lemma pairs_nonempty (R : Θ → D → ℝ) (g : Θ → ℝ) (eta : ℝ) (he : 0 ≤ eta) :
    (pairDistances R g eta).Nonempty := by
  let x : Θ := Classical.choice inferInstance
  refine ⟨0,mem_image.mpr ⟨(x,x),?_,by simp⟩⟩
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  intro i
  simp only [sub_self,abs_zero]
  linarith

def radius (R : Θ → D → ℝ) (g : Θ → ℝ) (eta : ℝ) (he : 0 ≤ eta) : ℝ :=
  (pairDistances R g eta).max' (pairs_nonempty R g eta he)/2

lemma pair_bound (R : Θ → D → ℝ) (g : Θ → ℝ) (eta : ℝ) (he : 0 ≤ eta)
    (x z : Θ) (h : Close R eta x z) : |g x-g z| ≤ 2*radius R g eta he := by
  have hm : |g x-g z| ∈ pairDistances R g eta := mem_image.mpr ⟨(x,z),by simp [h],rfl⟩
  have hh := le_max' _ _ hm
  dsimp [radius]
  linarith

def values (R : Θ → D → ℝ) (g : Θ → ℝ) (eta : ℝ) (y : D → ℝ) : Finset ℝ :=
  (univ.filter (fun x => Compatible R eta x y)).image g

def midpoint (R : Θ → D → ℝ) (g : Θ → ℝ) (eta : ℝ) (y : D → ℝ) : ℝ :=
  if h : (values R g eta y).Nonempty then
    ((values R g eta y).min' h+(values R g eta y).max' h)/2 else 0

theorem midpoint_error (R : Θ → D → ℝ) (g : Θ → ℝ) (eta : ℝ) (he : 0 ≤ eta)
    (x : Θ) (y : D → ℝ) (hx : Compatible R eta x y) :
    |midpoint R g eta y-g x| ≤ radius R g eta he := by
  have hxv : g x ∈ values R g eta y := mem_image.mpr ⟨x,by simp [hx],rfl⟩
  have hn : (values R g eta y).Nonempty := ⟨g x,hxv⟩
  have hlo := min'_le _ _ hxv
  have hhi := le_max' _ _ hxv
  obtain ⟨a,ha,hea⟩ := mem_image.mp (min'_mem (values R g eta y) hn)
  obtain ⟨b,hb,heb⟩ := mem_image.mp (max'_mem (values R g eta y) hn)
  have hc : Close R eta a b := (balls_intersect_iff R eta a b).mp
    ⟨y,(mem_filter.mp ha).2,(mem_filter.mp hb).2⟩
  have hp := pair_bound R g eta he a b hc
  have hp' := (abs_le.mp hp).1
  rw [hea,heb] at hp'
  unfold midpoint
  rw [dif_pos hn]
  apply abs_le.mpr
  constructor <;> linarith

def feasibleErrors (R : Θ → D → ℝ) (g : Θ → ℝ) (eta : ℝ) : Set ℝ :=
  {eps | ∃ psi : (D → ℝ) → ℝ, ∀ x y, Compatible R eta x y → |psi y-g x| ≤ eps}

theorem decoder_lower (R : Θ → D → ℝ) (g : Θ → ℝ) (eta eps : ℝ) (he : 0 ≤ eta)
    (h : eps ∈ feasibleErrors R g eta) : radius R g eta he ≤ eps := by
  obtain ⟨psi,hpsi⟩ := h
  obtain ⟨p,hp,heq⟩ := mem_image.mp (max'_mem _ (pairs_nonempty R g eta he))
  have hc := (mem_filter.mp hp).2
  obtain ⟨y,hy,hz⟩ := (balls_intersect_iff R eta p.1 p.2).mpr hc
  have h1 := hpsi p.1 y hy
  have h2 := hpsi p.2 y hz
  have ht := abs_sub_le (g p.1) (psi y) (g p.2)
  rw [abs_sub_comm (g p.1) (psi y)] at ht
  unfold radius
  rw [← heq]
  linarith

theorem resolution_minimax_exact (R : Θ → D → ℝ) (g : Θ → ℝ) (eta : ℝ) (he : 0 ≤ eta) :
    sInf (feasibleErrors R g eta) = radius R g eta he := by
  have hm : radius R g eta he ∈ feasibleErrors R g eta :=
    ⟨midpoint R g eta,fun x y h => midpoint_error R g eta he x y h⟩
  have hl := fun eps h => decoder_lower R g eta eps he h
  exact le_antisymm (csInf_le ⟨radius R g eta he,hl⟩ hm) (le_csInf ⟨_,hm⟩ hl)

#print axioms balls_intersect_iff
#print axioms pair_bound
#print axioms midpoint_error
#print axioms decoder_lower
#print axioms resolution_minimax_exact
end
end CIGAMF.P13.QueryResolutionMinimax
