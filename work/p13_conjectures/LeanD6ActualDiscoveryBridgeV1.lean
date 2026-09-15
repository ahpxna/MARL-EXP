import «LeanD6DiscoveryStoppingV1»

/-! Instantiation with the actual D6 world/query means. Anchor and helper indices
are independent of A and mu. Every coordinate is sampled by four legal queries;
all hypotheses about the contrast law are discharged by the construction. -/
namespace CIGAMF.P13.D6ActualDiscoveryBridge
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6NuisanceFreeDiscovery
open CIGAMF.P13.D6NuisanceFreeDiscoveryLaw
open CIGAMF.P13.D6DiscoveryVectorCertificate CIGAMF.P13.D6DiscoveryStopping
noncomputable section
variable {n : ℕ}

abbrev Off (j : I n) := {i : I n // i ≠ j}

/-- Helper indices exist from three off-j coordinates, independently of A. -/
theorem helper_exists (j : I n) (a : Off j) (hn : 3 ≤ Fintype.card (Off j)) :
    ∃ helper : Off j → Off j, (∀ i, a ≠ helper i) ∧ (∀ i, i ≠ helper i) := by
  have hh (i : Off j) : ∃ k : Off j, a ≠ k ∧ i ≠ k := by
    have hc : ({a,i} : Finset (Off j)).card < (univ : Finset (Off j)).card := by
      have hp : ({a,i} : Finset (Off j)).card ≤ 2 := by
        simpa using card_insert_le a ({i} : Finset (Off j))
      simp only [card_univ]
      omega
    have hnotsub : ¬ (univ : Finset (Off j)) ⊆ {a,i} := fun h => (not_lt_of_ge (card_le_card h)) hc
    obtain ⟨k,_,hk⟩ := not_subset.mp hnotsub
    refine ⟨k,?_,?_⟩
    · intro h;subst k;exact hk (by simp)
    · intro h;subst k;exact hk (by simp)
  choose helper hh using hh
  exact ⟨helper,fun i => (hh i).1,fun i => (hh i).2⟩

def encodedB (A : Finset (I n)) (j : I n) : Finset (Off j) := univ.filter (fun i => i.val ∉ A)

def means (A : Finset (I n)) (j : I n) (a : Off j) (helper : Off j → Off j) (mu : ℝ)
    (i : Off j) (t : Fin 4) : ℝ := actualMean A j mu (queries a.val i.val (helper i).val t)

lemma actual_design_legal (j : I n) (a : Off j) (helper : Off j → Off j)
    (ha : ∀ i, a ≠ helper i) (hi : ∀ i, i ≠ helper i) (q : ℝ) (hq : 2 ≤ q)
    (i : Off j) (t : Fin 4) : Legal j q (queries a.val i.val (helper i).val t) := by
  have ha' : a.val ≠ (helper i).val := fun h => ha i (Subtype.ext h)
  have hi' : i.val ≠ (helper i).val := fun h => hi i (Subtype.ext h)
  fin_cases t
  · trivial
  · trivial
  · exact pair_legal j i.val (helper i).val i.property (helper i).property hi' q hq
  · exact pair_legal j a.val (helper i).val a.property (helper i).property ha' q hq

lemma actual_mean_identity (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (a : Off j) (helper : Off j → Off j)
    (ha : ∀ i, a ≠ helper i) (hi : ∀ i, i ≠ helper i) (mu : ℝ) (i : Off j) :
    (∑ t,signs t*means A j a helper mu i t) = target (encodedB A j) a i := by
  have hh := actual_contrast A j a.val i.val (helper i).val hj a.property i.property
    (helper i).property (fun h => ha i (Subtype.ext h)) (fun h => hi i (Subtype.ext h)) mu
  have he : target (encodedB A j) a i=label A i.val-label A a.val := by
    simp only [target,encodedB,mem_filter,mem_univ,true_and,label]
    split_ifs <;> simp_all
  rw [he]
  simpa [means,queries,signs,Fin.sum_univ_succ,sub_eq_add_neg,add_assoc] using hh

/-- The algorithm takes q as input. The equation hq verifies its model size;
B and its membership are not inputs to stageAccept or queryCost. -/
theorem actual_discovery_terminates (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (a : Off j) (helper : Off j → Off j)
    (ha : ∀ i, a ≠ helper i) (hi : ∀ i, i ≠ helper i) (mu : ℝ)
    (q r0 : ℕ) (hq : (encodedB A j).card=q) (hr0 : 512 ≤ r0) :
    ∀ᵐ x ∂vectorPath (means A j a helper mu), ∃ s, stageAccept q r0 s x := by
  rw [← hq]
  exact discovery_terminates _ _ a (actual_mean_identity A j hj a helper ha hi mu) r0 hr0

theorem actual_discovery_finite_expectation (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (a : Off j) (helper : Off j → Off j)
    (ha : ∀ i, a ≠ helper i) (hi : ∀ i, i ≠ helper i) (mu : ℝ)
    (q r0 : ℕ) (hq : (encodedB A j).card=q) (hr0 : 512 ≤ r0) :
    (∫⁻ x,queryCost q r0 x ∂vectorPath (means A j a helper mu)) < ∞ := by
  rw [← hq]
  exact discovery_expected_cost_finite _ _ a (actual_mean_identity A j hj a helper ha hi mu) r0 hr0

theorem actual_discovery_expected_bound (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (a : Off j) (helper : Off j → Off j)
    (ha : ∀ i, a ≠ helper i) (hi : ∀ i, i ≠ helper i) (mu : ℝ)
    (q r0 : ℕ) (hq : (encodedB A j).card=q) (hr0 : 512 ≤ r0) :
    (∫⁻ x,queryCost q r0 x ∂vectorPath (means A j a helper mu)) ≤
      (4*Fintype.card (Off j)*r0:ℕ)*(1+2*eta (Fintype.card (Off j)) r0) := by
  rw [← hq]
  exact discovery_expected_cost _ _ a (actual_mean_identity A j hj a helper ha hi mu) r0 hr0

theorem actual_discovery_wrong_bound (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (a : Off j) (helper : Off j → Off j)
    (ha : ∀ i, a ≠ helper i) (hi : ∀ i, i ≠ helper i) (mu : ℝ)
    (q r0 : ℕ) (hq : (encodedB A j).card=q) (hr0 : 512 ≤ r0) :
    vectorPath (means A j a helper mu)
      (⋃ s,{x | ∃ S, Certified (repetitions r0 s) q x S ∧ S ≠ encodedB A j}) ≤
      eta (Fintype.card (Off j)) r0*(1-(4⁻¹:ℝ≥0∞))⁻¹ := by
  rw [← hq]
  exact discovery_ever_wrong _ _ a (actual_mean_identity A j hj a helper ha hi mu) r0 hr0

#print axioms helper_exists
#print axioms actual_design_legal
#print axioms actual_mean_identity
#print axioms actual_discovery_terminates
#print axioms actual_discovery_finite_expectation
#print axioms actual_discovery_expected_bound
#print axioms actual_discovery_wrong_bound
end
end CIGAMF.P13.D6ActualDiscoveryBridge
