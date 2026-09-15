import Mathlib

/-! R1: a new primitive of unit-variance edge-contrast observations.
Exposure is normalized over unordered edges. These are not scalar samples. -/
namespace CIGAMF.P13.FunctionalContrastDesign
open Finset
open scoped BigOperators
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

def mean (z : I → ℝ) := (∑ i,z i)/(Fintype.card I:ℝ)
def completeEnergy (z : I → ℝ) := (∑ a,∑ b,(z a-z b)^2)/(2*(Fintype.card I:ℝ)*((Fintype.card I:ℝ)-1))
def contrastEnergy (c : I → I → ℝ) (z : I → ℝ) := (∑ a,∑ b,c a b*(z a-z b)^2)/4
def Alternative (delta : ℝ) (z : I → ℝ) : Prop := ∃ a b,delta ≤ z a-z b
def completeCosts (delta : ℝ) : Set ℝ := {v | ∃ z : I → ℝ,Alternative delta z ∧ v=completeEnergy z}

lemma contrast_energy_nonneg (c : I → I → ℝ) (hc : ∀ a b,0 ≤ c a b) (z : I → ℝ) :
    0 ≤ contrastEnergy c z := by
  unfold contrastEnergy
  apply div_nonneg _ (by norm_num)
  exact sum_nonneg (fun a _ => sum_nonneg (fun b _ => mul_nonneg (hc a b) (sq_nonneg _)))

/-- A nontrivial zero cut yields an invisible capacity-changing alternative. -/
theorem disconnected_zero_information (c : I → I → ℝ) (S : Finset I)
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (hzero : ∀ a b,¬ (a ∈ S ↔ b ∈ S) → c a b=0)
    (delta : ℝ) :
    ∃ z : I → ℝ,Alternative delta z ∧ contrastEnergy c z=0 := by
  let z := fun i => if i ∈ S then delta else 0
  obtain ⟨a,ha⟩ := hS
  obtain ⟨b,hb⟩ := hSc
  have hb' : b ∉ S := mem_compl.mp hb
  refine ⟨z,⟨a,b,by simp [z,ha,hb']⟩,?_⟩
  unfold contrastEnergy
  have h : ∀ a b,c a b*(z a-z b)^2=0 := by
    intro a b
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
    · simp [z,ha,hb]
    · rw [hzero a b (by simp [ha,hb])];simp
    · rw [hzero a b (by simp [ha,hb])];simp
    · simp [z,ha,hb]
  simp [h]

lemma pair_sum_identity (z : I → ℝ) :
    (∑ a,∑ b,(z a-z b)^2)=2*(Fintype.card I:ℝ)*(∑ a,z a^2)-2*(∑ a,z a)^2 := by
  have h (a : I) : (∑ b,(z a-z b)^2)=
      (Fintype.card I:ℝ)*z a^2-2*z a*(∑ b,z b)+(∑ b,z b^2) := by
    simp only [sub_sq,sum_add_distrib,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,← mul_sum]
  simp_rw [h]
  simp only [sum_add_distrib,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,← sum_mul,← mul_sum]
  ring

/-- Twice the unordered complete-graph energy identity. -/
theorem complete_energy_identity (z : I → ℝ) :
    (∑ a,∑ b,(z a-z b)^2)=2*(Fintype.card I:ℝ)*(∑ a,(z a-mean z)^2) := by
  have hK : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card I ≠ 0)
  rw [pair_sum_identity]
  simp only [mean,sub_sq,sum_add_distrib,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,← sum_mul]
  field_simp
  <;> ring_nf
  <;> simp [← sum_mul,← mul_sum]
  <;> ring

lemma two_cell_variance_lower (z : I → ℝ) (a b : I) (hab : a ≠ b) :
    (z a-z b)^2/2 ≤ ∑ i,(z i-mean z)^2 := by
  have hs : (z a-mean z)^2+(z b-mean z)^2 ≤ ∑ i,(z i-mean z)^2 := by
    have h := sum_le_sum_of_subset_of_nonneg (s := ({a,b}:Finset I)) (t := univ)
      (subset_univ _) (fun i _ _ => sq_nonneg (z i-mean z))
    simpa [hab] using h
  nlinarith [sq_nonneg ((z a-mean z)+(z b-mean z))]

theorem complete_flat_lower (hK : 2 ≤ Fintype.card I) (delta : ℝ) (hd : 0 < delta)
    (z : I → ℝ) (hz : Alternative delta z) :
    delta^2/(2*((Fintype.card I:ℝ)-1)) ≤ completeEnergy z := by
  obtain ⟨a,b,habgap⟩ := hz
  have hab : a ≠ b := by intro h;subst b;simp at habgap;linarith
  have h := two_cell_variance_lower z a b hab
  have hKr : (2:ℝ) ≤ Fintype.card I := by exact_mod_cast hK
  have hKm : 0 < (Fintype.card I:ℝ)-1 := by linarith
  unfold completeEnergy
  rw [complete_energy_identity]
  apply (div_le_div_iff₀ (by positivity : 0<2*((Fintype.card I:ℝ)-1)) (by positivity : 0<2*(Fintype.card I:ℝ)*((Fintype.card I:ℝ)-1))).mpr
  have hh : delta^2 ≤ 2*∑ i,(z i-mean z)^2 := by nlinarith
  nlinarith [mul_nonneg (show 0 ≤ 2*(Fintype.card I:ℝ)*((Fintype.card I:ℝ)-1) by positivity) (show 0 ≤ 2*(∑ i,(z i-mean z)^2)-delta^2 by linarith)]

/-- The flat lower bound is attained by two opposite endpoints and zeros. -/
theorem complete_flat_attained (a b : I) (hab : a ≠ b) (delta : ℝ) :
    ∃ z : I → ℝ,Alternative delta z ∧
      completeEnergy z=delta^2/(2*((Fintype.card I:ℝ)-1)) := by
  let z : I → ℝ := fun i => if i=a then delta/2 else if i=b then -delta/2 else 0
  have hfilter : (univ.filter (fun i : I => i=a))={a} := by ext i; simp
  have hzsum : (∑ i,z i)=0 := by simp [z,Finset.sum_ite,hab,hab.symm,hfilter]; ring
  have hzsq : (∑ i,(z i)^2)=delta^2/2 := by
    simp only [z,ite_pow]
    simp [Finset.sum_ite,hab,hab.symm,hfilter]
    <;> ring
  have hK : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card I ≠ 0)
  refine ⟨z,⟨a,b,by simp [z,hab,hab.symm];linarith⟩,?_⟩
  unfold completeEnergy
  rw [pair_sum_identity,hzsum,hzsq]
  field_simp
  <;> ring

#print axioms contrast_energy_nonneg
#print axioms disconnected_zero_information
#print axioms complete_energy_identity
#print axioms complete_flat_lower
#print axioms complete_flat_attained
end
end CIGAMF.P13.FunctionalContrastDesign
