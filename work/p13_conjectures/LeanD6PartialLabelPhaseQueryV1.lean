import «LeanD6GaussianQueryDominanceV1»

/-! Margin learning need not know the complete hidden label: any certified
subset of B supplies a label-invariant legal Gaussian experiment. In the
one-unresolved-swap construction it has size q-1, hence sensitivity q-1. -/
namespace CIGAMF.P13.D6PartialLabelPhaseQuery
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationFiniteBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6PhaseTestingInformation
open CIGAMF.P13.D6GaussianQueryDominance
noncomputable section
variable {n : ℕ}

theorem common_B_query (A G : Finset (I n)) (j : I n) (q d mu : ℝ)
    (hj : j ∉ A) (hG : G ⊆ others A j) (hsize : (G.card : ℝ)=d)
    (hd : 2 ≤ d) (hdq : d ≤ q) :
    Legal j q (.inr (G,false)) ∧ actualMean A j mu (.inr (G,false))=1+d-d*mu := by
  have hjG : j ∉ G := by
    intro h
    have hh := hG h
    simpa [others] using hh
  have hn : 2 ≤ G.card := by exact_mod_cast (show (2:ℝ) ≤ G.card by linarith)
  have he : G ∩ others A j=G := inter_eq_left.mpr hG
  refine ⟨⟨hjG,by linarith,by intro _;exact hn⟩,?_⟩
  change world A j mu (query G j false)=_
  rw [actual_query_mean A G j false hj hjG (by intro _;exact hn),he,hsize]
  simp only [bit_false,Bool.false_eq_true,↓reduceIte,sub_zero]
  ring

theorem common_B_information (A G : Finset (I n)) (j : I n) (q d mu nu : ℝ)
    (hj : j ∉ A) (hG : G ⊆ others A j) (hsize : (G.card : ℝ)=d)
    (hd : 2 ≤ d) (hdq : d ≤ q) :
    information A A j mu nu (.inr (G,false))=d^2*(mu-nu)^2/2 := by
  have hl := (common_B_query A G j q d mu hj hG hsize hd hdq).1
  change queryKL A A G j false mu nu=_
  rw [same_set_joint_information A G j false hj hl.1 hl.2.2,
    inter_eq_left.mpr hG,hsize]
  simp only [bit_false,sub_zero]
  ring

/-- Simultaneously valid for every still-possible label, using exactly the same
query G. The Gaussian observation law therefore does not reveal which such
label is true, while retaining sensitivity equal to the certified B core. -/
theorem unresolved_family_phase_law (W : Finset (Finset (I n))) (G : Finset (I n))
    (j : I n) (q d : ℝ) (hsize : (G.card : ℝ)=d) (hd : 2 ≤ d) (hdq : d ≤ q)
    (hj : ∀ A ∈ W,j ∉ A) (hcommon : ∀ A ∈ W,G ⊆ others A j) :
    ∀ A ∈ W,∀ mu : ℝ,
      ProbabilityTheory.gaussianReal (actualMean A j mu (.inr (G,false))) 1 =
        ProbabilityTheory.gaussianReal (1+d-d*mu) 1 := by
  intro A hA mu
  rw [(common_B_query A G j q d mu (hj A hA) (hcommon A hA) hsize hd hdq).2]

/-- Losing one known B coordinate changes squared sensitivity from q² to
(q-1)², with the exact relative loss displayed. -/
theorem one_swap_information_ratio (q : ℝ) (hq : q ≠ 0) :
    (q-1)^2/q^2=1-2/q+1/q^2 := by
  field_simp [hq]
  <;> ring

#print axioms common_B_query
#print axioms common_B_information
#print axioms unresolved_family_phase_law
#print axioms one_swap_information_ratio
end
end CIGAMF.P13.D6PartialLabelPhaseQuery
