import «LeanD6ActualDiscoveryBridgeV1»
import «LeanD6StoppingGeometryBridgeV1»

/-! A terminating discovery decoder with an anytime error bound for literal D6
support geometry. This closes this standalone decoder, not the Gamma-optimal
allocation tracker. A certified off-j B-set returns B union {j}. -/
namespace CIGAMF.P13.D6DiscoveryGeometry
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6UniqueOptimum
open CIGAMF.P13.D6StoppingGeometryBridge
open CIGAMF.P13.D6DiscoveryVectorCertificate CIGAMF.P13.D6DiscoveryStopping
open CIGAMF.P13.D6ActualDiscoveryBridge
noncomputable section
variable {n : ℕ}

def embedding (j : I n) : Off j ↪ I n := ⟨Subtype.val,Subtype.val_injective⟩
def selection (j : I n) (S : Finset (Off j)) : Finset (I n) := insert j (S.map (embedding j))

lemma encodedB_map (A : Finset (I n)) (j : I n) :
    (encodedB A j).map (embedding j)=others A j := by
  ext i
  simp [encodedB,embedding,others]
  tauto

lemma true_selection (A : Finset (I n)) (j : I n) (hj : j ∉ A) :
    selection j (encodedB A j)=Aᶜ := by
  rw [selection,encodedB_map]
  ext i
  by_cases hi : i=j
  · subst i;simp [hj]
  · simp [others,hi]

lemma model_card (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (A : Finset (I (2*r+1))) (hA : A ∈ worlds r j) : (encodedB A j).card=r := by
  have hp := world_parameters r j hr hA
  have he := congrArg Finset.card (encodedB_map A j)
  rw [card_map] at he
  rw [he]
  unfold others
  rw [card_erase_of_mem (by simp [hp.1])]
  have hc : (univ \ A).card=Aᶜ.card := rfl
  rw [hc,hp.2.2.1,hp.2.1]
  omega

lemma true_selection_geometric (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (A : Finset (I (2*r+1))) (hA : A ∈ worlds r j) (mu : ℝ)
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    GeometricOptimal A (selection j (encodedB A j)) j mu := by
  have hp := world_parameters r j hr hA
  rw [true_selection A j hp.1]
  exact (geometric_optimal_iff A Aᶜ j hp.1 mu hmu hmu1 hp.2.2.1 hp.2.2.1 hp.2.2.2).mpr rfl

/-- Full world parameters discharge the discovery cardinality premise. -/
theorem decoder_terminates (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (A : Finset (I (2*r+1))) (hA : A ∈ worlds r j)
    (a : Off j) (helper : Off j → Off j)
    (ha : ∀ i, a ≠ helper i) (hi : ∀ i, i ≠ helper i) (mu : ℝ)
    (r0 : ℕ) (hr0 : 512 ≤ r0) :
    ∀ᵐ x ∂vectorPath (means A j a helper mu), ∃ s, stageAccept r r0 s x := by
  exact actual_discovery_terminates A j (world_parameters r j hr hA).1 a helper ha hi mu
    r r0 (model_card r j hr A hA) hr0

theorem decoder_expected_cost_finite (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (A : Finset (I (2*r+1))) (hA : A ∈ worlds r j)
    (a : Off j) (helper : Off j → Off j)
    (ha : ∀ i, a ≠ helper i) (hi : ∀ i, i ≠ helper i) (mu : ℝ)
    (r0 : ℕ) (hr0 : 512 ≤ r0) :
    (∫⁻ x,queryCost r r0 x ∂vectorPath (means A j a helper mu)) < ∞ := by
  exact actual_discovery_finite_expectation A j (world_parameters r j hr hA).1 a helper ha hi mu
    r r0 (model_card r j hr A hA) hr0

theorem decoder_anytime_geometric_error (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (A : Finset (I (2*r+1))) (hA : A ∈ worlds r j)
    (a : Off j) (helper : Off j → Off j)
    (ha : ∀ i, a ≠ helper i) (hi : ∀ i, i ≠ helper i) (mu : ℝ)
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (r0 : ℕ) (hr0 : 512 ≤ r0) :
    vectorPath (means A j a helper mu)
      (⋃ s,{x | ∃ S, Certified (repetitions r0 s) r x S ∧ ¬GeometricOptimal A (selection j S) j mu}) ≤
      eta (Fintype.card (Off j)) r0*(1-(4⁻¹:ℝ≥0∞))⁻¹ := by
  apply (measure_mono ?_).trans (actual_discovery_wrong_bound A j (world_parameters r j hr hA).1
    a helper ha hi mu r r0 (model_card r j hr A hA) hr0)
  intro x hx
  obtain ⟨s,hs⟩ := Set.mem_iUnion.mp hx
  obtain ⟨S,hS,hbad⟩ := hs
  apply Set.mem_iUnion.mpr
  refine ⟨s,S,hS,?_⟩
  intro he
  subst S
  exact hbad (true_selection_geometric r j hr A hA mu hmu hmu1)

#print axioms model_card
#print axioms true_selection_geometric
#print axioms decoder_terminates
#print axioms decoder_expected_cost_finite
#print axioms decoder_anytime_geometric_error
end
end CIGAMF.P13.D6DiscoveryGeometry
