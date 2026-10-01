import «LeanFunctionalContrastDesignV1»
namespace CIGAMF.P13.FunctionalContrastInfimum
open Finset
open CIGAMF.P13.FunctionalContrastDesign
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

theorem complete_information_exact (hK : 2 ≤ Fintype.card I) (delta : ℝ) (hd : 0<delta) :
    IsLeast (completeCosts (I:=I) delta) (delta^2/(2*((Fintype.card I:ℝ)-1))) := by
  obtain ⟨a,b,hab⟩ := Fintype.one_lt_card_iff.mp (show 1 < Fintype.card I by omega)
  obtain ⟨z,hz,he⟩ := complete_flat_attained a b hab delta
  refine ⟨⟨z,hz,he.symm⟩,?_⟩
  rintro v ⟨z,hz,rfl⟩
  exact complete_flat_lower hK delta hd z hz

theorem complete_information_sInf (hK : 2 ≤ Fintype.card I) (delta : ℝ) (hd : 0<delta) :
    sInf (completeCosts (I:=I) delta)=delta^2/(2*((Fintype.card I:ℝ)-1)) :=
  (complete_information_exact hK delta hd).csInf_eq

/-- Exact zero infimum on any nontrivial zero cut. No positivity on within-cut
edges beyond nonnegativity, and no fictitious inverse for a disconnected graph. -/
theorem disconnected_infimum (c : I → I → ℝ) (hc : ∀ a b,0 ≤ c a b)
    (S : Finset I) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (hzero : ∀ a b,¬(a ∈ S ↔ b ∈ S) → c a b=0) (delta : ℝ) :
    IsLeast {v | ∃ z : I → ℝ,Alternative delta z ∧ v=contrastEnergy c z} 0 := by
  obtain ⟨z,hz,he⟩ := disconnected_zero_information c S hS hSc hzero delta
  refine ⟨⟨z,hz,he.symm⟩,?_⟩
  rintro v ⟨z,_,rfl⟩
  exact contrast_energy_nonneg c hc z

#print axioms complete_information_exact
#print axioms complete_information_sInf
#print axioms disconnected_infimum
end
end CIGAMF.P13.FunctionalContrastInfimum
