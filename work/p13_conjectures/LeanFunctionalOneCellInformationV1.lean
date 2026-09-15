import Mathlib

namespace CIGAMF.P13.FunctionalOneCellInformation
open scoped BigOperators
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {R A : Type*} [Fintype R] [Fintype A] [DecidableEq R] [DecidableEq A]

def Crosses (T : Finset R) (C : ℝ) (lambda : R → A → ℝ) : Prop :=
  ∃ j,j ∉ T ∧ ∃ a b,a ≠ b ∧ C ≤ lambda j a-lambda j b

def StrictCrosses (T : Finset R) (C : ℝ) (lambda : R → A → ℝ) : Prop :=
  ∃ j,j ∉ T ∧ ∃ a b,a ≠ b ∧ C < lambda j a-lambda j b

def energy (theta w variance lambda : R → A → ℝ) : ℝ :=
  ∑ j,∑ a,w j a*(lambda j a-theta j a)^2/(2*variance j a)

def shift (theta : R → A → ℝ) (j : R) (a : A) (d : ℝ) : R → A → ℝ :=
  fun k b => theta k b+if k=j ∧ b=a then d else 0

theorem one_cell_flip (theta : R → A → ℝ) (T : Finset R) (C : ℝ)
    (j : R) (a b : A) (hj : j ∉ T) (hab : a ≠ b) :
    Crosses T C (shift theta j a (C+theta j b-theta j a)) := by
  refine ⟨j,hj,a,b,hab,?_⟩
  simp [shift,hab,hab.symm]
  <;> linarith

theorem one_cell_energy (theta w variance : R → A → ℝ) (j : R) (a : A) (d : ℝ) :
    energy theta w variance (shift theta j a d) = w j a*d^2/(2*variance j a) := by
  unfold energy shift
  simp only [add_sub_cancel_left]
  have hf : ∀ k b,w k b*(if k=j ∧ b=a then d else 0)^2/(2*variance k b) =
      if k=j then (if b=a then w j a*d^2/(2*variance j a) else 0) else 0 := by
    intro k b
    by_cases hk : k=j <;> by_cases hb : b=a <;> simp [hk,hb]
  simp_rw [hf]
  simp

def costs (theta w variance : R → A → ℝ) (P : (R → A → ℝ) → Prop) : Set ℝ :=
  {v | ∃ lambda,P lambda ∧ v=energy theta w variance lambda}

def information (theta w variance : R → A → ℝ) (P : (R → A → ℝ) → Prop) : ℝ :=
  sInf (costs theta w variance P)

lemma costs_nonneg (theta w variance : R → A → ℝ) (hw : ∀ j a,0 ≤ w j a)
    (hv : ∀ j a,0 < variance j a) (P : (R → A → ℝ) → Prop) :
    BddBelow (costs theta w variance P) := by
  refine ⟨0,?_⟩
  rintro _ ⟨lambda,_,rfl⟩
  exact sum_nonneg (fun j _ => sum_nonneg (fun a _ =>
    div_nonneg (mul_nonneg (hw j a) (sq_nonneg _)) (mul_nonneg (by norm_num) (hv j a).le)))

theorem one_cell_information_upper (theta w variance : R → A → ℝ)
    (hw : ∀ j a,0 ≤ w j a) (hv : ∀ j a,0 < variance j a)
    (T : Finset R) (C : ℝ) (j : R) (a b : A) (hj : j ∉ T) (hab : a ≠ b) :
    information theta w variance (Crosses T C) ≤
      w j a*(C+theta j b-theta j a)^2/(2*variance j a) := by
  rw [← one_cell_energy theta w variance j a]
  exact csInf_le (costs_nonneg theta w variance hw hv _) ⟨_,one_cell_flip theta T C j a b hj hab,rfl⟩

theorem strict_one_cell_information_upper (theta w variance : R → A → ℝ)
    (hw : ∀ j a,0 ≤ w j a) (hv : ∀ j a,0 < variance j a)
    (T : Finset R) (C : ℝ) (j : R) (a b : A) (hj : j ∉ T) (hab : a ≠ b) :
    information theta w variance (StrictCrosses T C) ≤
      w j a*(C+theta j b-theta j a)^2/(2*variance j a) := by
  let I := information theta w variance (StrictCrosses T C)
  let d := C+theta j b-theta j a
  have hbound : Set.Ioi (0:ℝ) ⊆ {u | I ≤ w j a*(d+u)^2/(2*variance j a)} := by
    intro u hu
    have hu0 : 0 < u := hu
    have hcross : StrictCrosses T C (shift theta j a (d+u)) := by
      refine ⟨j,hj,a,b,hab,?_⟩
      simp [shift,hab,hab.symm,d]
      <;> linarith [hu0]
    have hh := csInf_le (costs_nonneg theta w variance hw hv _) ⟨_,hcross,rfl⟩
    rwa [one_cell_energy] at hh
  have hc := closure_minimal hbound (isClosed_le continuous_const (by fun_prop))
  rw [closure_Ioi] at hc
  have hh := hc (show (0:ℝ) ∈ Set.Ici 0 by simp)
  simpa [I,d] using hh

theorem outsider_cell_positive (theta w variance : R → A → ℝ)
    (hw : ∀ j a,0 ≤ w j a) (hv : ∀ j a,0 < variance j a)
    (T : Finset R) (C : ℝ) (hI : 0 < information theta w variance (StrictCrosses T C))
    (j : R) (a b : A) (hj : j ∉ T) (hab : a ≠ b) : 0 < w j a := by
  have hh := strict_one_cell_information_upper theta w variance hw hv T C j a b hj hab
  by_contra h
  have he : w j a=0 := le_antisymm (le_of_not_gt h) (hw j a)
  rw [he,zero_mul,zero_div] at hh
  linarith

/-- Sum of all mandatory outsider-cell masses, with positive displacement and variance. -/
theorem mandatory_mass_bound {E : Type*} [Fintype E] (w d v : E → ℝ) (J : ℝ)
    (hd : ∀ e,0 < d e) (hv : ∀ e,0 < v e) (hbudget : ∑ e,w e ≤ 1)
    (hupper : ∀ e,J ≤ w e*(d e)^2/(2*v e)) :
    J*(∑ e,2*v e/(d e)^2) ≤ 1 := by
  have hcell : ∀ e,J*(2*v e/(d e)^2) ≤ w e := by
    intro e
    have hh := (le_div_iff₀ (show 0<2*v e from mul_pos (by norm_num) (hv e))).mp (hupper e)
    have he : J*(2*v e/(d e)^2) = (J*(2*v e))/(d e)^2 := by ring
    rw [he]
    exact (div_le_iff₀ (sq_pos_of_pos (hd e))).mpr hh
  have hsum := sum_le_sum (fun e (_ : e ∈ univ) => hcell e)
  rw [← mul_sum] at hsum
  exact hsum.trans hbudget

#print axioms one_cell_flip
#print axioms one_cell_energy
#print axioms one_cell_information_upper
#print axioms strict_one_cell_information_upper
#print axioms outsider_cell_positive
#print axioms mandatory_mass_bound
end
end CIGAMF.P13.FunctionalOneCellInformation
