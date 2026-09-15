import «LeanD6RevalidationRegretBridgeV1»

/-! Certificates determine a unique top-q set on every observation vector.
This removes ambiguity in the Classical.choose recommendation and proves its
level sets measurable, including the no-certificate fallback. -/
namespace CIGAMF.P13.D6RecommendationMeasurability
open scoped ENNReal
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6DiscoveryVectorCertificate CIGAMF.P13.D6RepeatedDiscovery
open CIGAMF.P13.D6RevalidationRegretBridge
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6LocalOracleRegret CIGAMF.P13.D6ActualDiscoveryBridge
noncomputable section
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma certified_unique (r q : ℕ) (x : Sample J) (S T : Finset J)
    (hS : Certified r q x S) (hT : Certified r q x T) : S=T := by
  have hcard : S.card=T.card := hS.1.trans hT.1.symm
  apply eq_of_subset_of_card_le ?_ hcard.ge
  intro i hi
  by_contra hit
  have hn : ¬ T ⊆ S := by
    intro h
    have he : T=S := eq_of_subset_of_card_le h hcard.le
    exact hit (he.symm ▸ hi)
  obtain ⟨j,hjt,hjs⟩ := not_subset.mp hn
  have h1 := hS.2 i hi j hjs
  have h2 := hT.2 j hjt i hit
  linarith

lemma certified_measurable (r q : ℕ) (S : Finset J) :
    MeasurableSet {x : Sample J | Certified r q x S} := by
  by_cases hS : S.card=q
  · simp only [Certified,hS,true_and,Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ : i ∈ S =>
      MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ : j ∉ S =>
        measurableSet_lt ((score_measurable r j).add_const _) (score_measurable r i)))))
  · simp [Certified,hS]

theorem recommendation_eq_iff (r q : ℕ) (x : Sample J) (S : Finset J) :
    recommendation q r x=S ↔ Certified r q x S ∨ (S=∅ ∧ ¬ accepts r q x) := by
  by_cases ha : accepts r q x
  · rw [recommendation,dif_pos ha]
    constructor
    · intro h
      exact Or.inl (h ▸ Classical.choose_spec ha)
    · rintro (hS | ⟨_,hn⟩)
      · exact certified_unique r q x _ S (Classical.choose_spec ha) hS
      · exact False.elim (hn ha)
  · simp [recommendation,ha,show ¬ Certified r q x S from fun h => ha ⟨S,h⟩,eq_comm]

theorem recommendation_level_measurable (r q : ℕ) (S : Finset J) :
    MeasurableSet {x : Sample J | recommendation q r x=S} := by
  simp_rw [recommendation_eq_iff]
  by_cases hS : S=∅
  · simp only [hS,true_and,Set.setOf_or]
    exact (certified_measurable r q ∅).union (accepts_measurable r q).compl
  · simpa only [hS,false_and,or_false] using certified_measurable r q S

theorem wrong_epoch_work_measurable (B : Finset J) (r0 : ℕ) :
    Measurable (wrongEpochWork B r0) := by
  unfold wrongEpochWork
  apply Measurable.ennreal_tsum
  intro s
  exact measurable_const.indicator (recommendation_level_measurable (epochSamples r0 s) B.card B).compl

/-- For measurable per-epoch actual oracle losses, the accumulated bad-label
loss is a measurable random variable, so its lintegral is an expectation. -/
theorem bad_regret_work_measurable {n : ℕ} (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (E : Finset (Measurement n)) (w : ℕ → Sample (Off j) → Measurement n → ℝ)
    (hloss : ∀ s,Measurable (fun x => oracleRegret A j q mu E (w s x))) (r0 : ℕ) :
    Measurable (badRegretWork A j q mu E w r0) := by
  unfold badRegretWork
  apply Measurable.ennreal_tsum
  intro s
  apply measurable_const.mul
  exact (ENNReal.measurable_ofReal.comp (hloss s)).indicator
    (recommendation_level_measurable (epochSamples r0 s) (encodedB A j).card (encodedB A j)).compl

#print axioms certified_unique
#print axioms recommendation_eq_iff
#print axioms recommendation_level_measurable
#print axioms wrong_epoch_work_measurable
#print axioms bad_regret_work_measurable
end
end CIGAMF.P13.D6RecommendationMeasurability
