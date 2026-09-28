import «LeanSupportUnboundedObstructionV1»
import «LeanTypedCertificateCompletionV1»

/-! Physical membership and exact normalization for the support obstruction.
Instantiates MASTER's certificate contract with a proved support-radius bound. -/
namespace CIGAMF.P13.SupportPhysicalQueryContract
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V6.FunctionalRanking
open CIGAMF.P13.SupportUnboundedObstruction
open CIGAMF.P13.TypedCertificateCompletion
noncomputable section
variable {m : ℕ}

def support (w : Fin m) : Finset (Fin m → ℝ) := {0,tip w}

lemma tip_ne_zero (w : Fin m) : tip w ≠ 0 := by
  intro h
  have hs := total_tip w
  rw [h] at hs
  simpa using hs

lemma tip_injective (hm : 2 ≤ m) : Function.Injective (@tip m) := by
  intro a b hab
  by_contra hne
  have h := congrFun hab a
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  simp [tip,hne] at h
  linarith

theorem physical_membership_iff (hm : 2 ≤ m) (a w : Fin m) :
    tip a ∈ support w ↔ w=a := by
  simp only [support,mem_insert,mem_singleton]
  rw [or_iff_right (tip_ne_zero a)]
  exact ⟨fun h => (tip_injective hm h).symm,fun h => by rw [h]⟩

def query (a w : Fin m) : Bool := decide (tip a ∈ support w)

theorem query_eq_answer (hm : 2 ≤ m) (a w : Fin m) : query a w = answer a w := by
  simp [query,answer,physical_membership_iff hm]

theorem physical_query_sound (hm : 2 ≤ m) (a b : Fin m) (hab : a ≠ b) (w : Fin m) :
    selectedRadius (worldF w) {choose a b (query a w)} = 0 := by
  rw [query_eq_answer hm]
  exact one_query_sound hm a b hab w

lemma component_osc (w j : Fin m) : osc (worldF w j) = |tip w j| := by
  have h0 : worldF w j 0 = 0 := rfl
  have h1 : worldF w j 1 = tip w j := by simp [worldF,supportPoint]
  rw [osc,maxVal_fin2,minVal_fin2,h0,h1]
  rcases le_total (0:ℝ) (tip w j) with h | h
  · rw [max_eq_right h,min_eq_left h,abs_of_nonneg h];ring
  · rw [max_eq_left h,min_eq_right h,abs_of_nonpos h];ring

/-- This is the sum of actual component radii, not a stipulated normalizer. -/
theorem total_component_radius (hm : 2 ≤ m) (w : Fin m) :
    (∑ j,osc (worldF w j)/2) = ((2:ℝ)*m-3)/2 := by
  have ht (j : Fin m) : |tip w j| = 1 + if j=w then (m:ℝ)-3 else 0 := by
    have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
    by_cases h : j=w
    · simp only [tip,h,↓reduceIte]
      rw [abs_of_nonpos (by linarith)]
      ring
    · simp [tip,h]
  simp_rw [component_osc,ht]
  rw [← sum_div]
  simp [sum_add_distrib]
  <;> ring

def concreteContract (hm : 2 ≤ m) (a b : Fin m) (hab : a ≠ b)
    (w : Fin m) (observed : Bool) : CertificateContract (Fin m) Unit where
  selected := choose a b observed
  epsilon := 0
  regret := fun j => selectedRadius (worldF w) {j}
  required := univ
  obligationHolds := fun _ => observed = query a w
  sound := by
    intro h
    have hh := h () (mem_univ ())
    rw [hh,physical_query_sound hm a b hab w]

/-- The concrete contract imports observation correctness only. Its regret
implication is discharged by physical_query_sound, not assumed as a field input. -/
theorem concrete_contract_sound (hm : 2 ≤ m) (a b : Fin m) (hab : a ≠ b)
    (w : Fin m) (observed : Bool) (hobs : observed = query a w) :
    (concreteContract hm a b hab w observed).regret
      (concreteContract hm a b hab w observed).selected ≤ 0 := by
  exact (concreteContract hm a b hab w observed).sound (fun _ _ => hobs)

#print axioms physical_membership_iff
#print axioms physical_query_sound
#print axioms total_component_radius
#print axioms concrete_contract_sound
end
end CIGAMF.P13.SupportPhysicalQueryContract
