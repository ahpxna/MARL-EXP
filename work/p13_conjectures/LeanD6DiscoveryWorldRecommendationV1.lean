import «LeanD6DiscoveryGeometryV1»
import «LeanD6RecommendationMeasurabilityV1»

/-! A total world-valued decoder. Its inputs are observations, q, j, and a
fixed feasible fallback; the true A is not an input. The decoder is re-evaluated
at each sample count rather than committing permanently after one certificate. -/
namespace CIGAMF.P13.D6DiscoveryWorldRecommendation
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6ActualDiscoveryBridge CIGAMF.P13.D6DiscoveryGeometry
open CIGAMF.P13.D6DiscoveryVectorCertificate CIGAMF.P13.D6RepeatedDiscovery
open CIGAMF.P13.D6RecommendationMeasurability
noncomputable section
attribute [local instance] Classical.propDecidable

lemma encoded_injective {n : ℕ} (j : I n) (A W : Finset (I n))
    (ha : j ∉ A) (hw : j ∉ W) (h : encodedB A j=encodedB W j) : A=W := by
  have hh := congrArg (selection j) h
  rw [true_selection A j ha,true_selection W j hw] at hh
  exact compl_injective hh

def candidate (q : ℕ) (j : I (2*q+1)) (fallback : Finset (I (2*q+1)))
    (r : ℕ) (x : Sample (Off j)) : Finset (I (2*q+1)) :=
  if h : ∃ W,W ∈ worlds q j ∧ encodedB W j=recommendation q r x
  then Classical.choose h else fallback

lemma candidate_valid (q : ℕ) (j : I (2*q+1)) (fallback : Finset (I (2*q+1)))
    (hf : fallback ∈ worlds q j) (r : ℕ) (x : Sample (Off j)) :
    candidate q j fallback r x ∈ worlds q j := by
  unfold candidate
  split
  · rename_i h
    exact (Classical.choose_spec h).1
  · exact hf

lemma candidate_correct (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (fallback A : Finset (I (2*q+1))) (hA : A ∈ worlds q j)
    (r : ℕ) (x : Sample (Off j)) (hr : recommendation q r x=encodedB A j) :
    candidate q j fallback r x=A := by
  have hex : ∃ W,W ∈ worlds q j ∧ encodedB W j=recommendation q r x := ⟨A,hA,hr.symm⟩
  unfold candidate
  rw [dif_pos hex]
  have hc := Classical.choose_spec hex
  exact encoded_injective j _ A (world_parameters q j (by omega) hc.1).1
    (world_parameters q j (by omega) hA).1 (hc.2.trans hr)

/-- Correct on the Gaussian coordinate-good event. This discharges the
structural decoder premise of the random-label regret theorem. -/
theorem candidate_correct_on_good (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (fallback A : Finset (I (2*q+1))) (hA : A ∈ worlds q j)
    (a : Off j) (r : ℕ) (x : Sample (Off j)) (hx : x ∉ bad (encodedB A j) a r) :
    candidate q j fallback r x=A := by
  apply candidate_correct q hq j fallback A hA r x
  have hh := recommendation_correct_on_good (encodedB A j) a r x hx
  rwa [model_card q j (by omega) A hA] at hh

lemma candidate_eq_iff (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (fallback W : Finset (I (2*q+1))) (r : ℕ) (x : Sample (Off j)) :
    candidate q j fallback r x=W ↔
      (W ∈ worlds q j ∧ recommendation q r x=encodedB W j) ∨
      (W=fallback ∧ ¬∃ V,V ∈ worlds q j ∧ recommendation q r x=encodedB V j) := by
  by_cases hex : ∃ V,V ∈ worlds q j ∧ encodedB V j=recommendation q r x
  · have hnone : ¬(¬∃ V,V ∈ worlds q j ∧ recommendation q r x=encodedB V j) := by
      intro hn
      obtain ⟨V,hV,he⟩ := hex
      exact hn ⟨V,hV,he.symm⟩
    constructor
    · intro h
      left
      unfold candidate at h
      rw [dif_pos hex] at h
      have hc := Classical.choose_spec hex
      rw [h] at hc
      exact ⟨hc.1,hc.2.symm⟩
    · rintro (⟨hw,hr⟩ | ⟨_,hn⟩)
      · exact candidate_correct q hq j fallback W hw r x hr
      · exact False.elim (hnone hn)
  · have hn : ¬∃ V,V ∈ worlds q j ∧ recommendation q r x=encodedB V j := by
      rintro ⟨V,hV,he⟩
      exact hex ⟨V,hV,he.symm⟩
    rw [candidate,dif_neg hex]
    constructor
    · intro h;exact Or.inr ⟨h.symm,hn⟩
    · rintro (⟨hw,hr⟩ | ⟨he,_⟩)
      · exact False.elim (hn ⟨W,hw,hr⟩)
      · exact he.symm

/-- Every level set of the finite world recommendation is measurable. -/
theorem candidate_level_measurable (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (fallback W : Finset (I (2*q+1))) (r : ℕ) :
    MeasurableSet {x | candidate q j fallback r x=W} := by
  simp only [candidate_eq_iff q hq j fallback W r]
  apply MeasurableSet.union
  · exact (MeasurableSet.const _).inter (recommendation_level_measurable r q (encodedB W j))
  · apply (MeasurableSet.const _).inter
    have hh : MeasurableSet {x : Sample (Off j) | ∃ V,V ∈ worlds q j ∧ recommendation q r x=encodedB V j} := by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion (fun V => (MeasurableSet.const _).inter
        (recommendation_level_measurable r q (encodedB V j)))
    exact hh.compl

#print axioms candidate_valid
#print axioms candidate_correct_on_good
#print axioms candidate_eq_iff
#print axioms candidate_level_measurable
end
end CIGAMF.P13.D6DiscoveryWorldRecommendation
