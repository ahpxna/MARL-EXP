import «LeanD6DiscoveryStoppingV1»
import Mathlib.Probability.Process.HittingTime

/-! The discovery certificate is observed at the END of its data block.
This connects its existing concentration/expected-work results to an actual
first-acceptance stopping time. It is not settleIndex, and is not a Gamma-rate
or termination theorem for a separate allocation likelihood certificate. -/
namespace CIGAMF.P13.D6DiscoveryStoppingTime
open scoped BigOperators ENNReal
open Finset MeasureTheory
open CIGAMF.P13.D6DiscoveryVectorCertificate CIGAMF.P13.D6DiscoveryStopping
open CIGAMF.P13.DyadicCertifiedStopping
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

def observedScores (r0 s : ℕ) (x : Sample I) : I → ℝ := score (repetitions r0 s) x

lemma observedScores_measurable (r0 s : ℕ) : Measurable (observedScores (I:=I) r0 s) :=
  measurable_pi_lambda _ (fun i => score_measurable _ i)

/-- This filtration contains only observed finite-prefix score summaries. -/
def scoreFiltration (r0 : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (Sample I)) :=
  Filtration.natural (observedScores r0) (fun s => (observedScores_measurable r0 s).stronglyMeasurable)

def acceptSet (q : ℕ) : Set (I → ℝ) :=
  {v | ∃ S : Finset I,S.card=q ∧ ∀ i ∈ S,∀ j ∉ S,v j+1/2<v i}

lemma acceptSet_measurable (q : ℕ) : MeasurableSet (acceptSet (I:=I) q) := by
  simp only [acceptSet,Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro S
  by_cases hS : S.card=q
  · simp only [hS,true_and,Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ : i ∈ S =>
      MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ : j ∉ S =>
        measurableSet_lt ((measurable_pi_apply j).add_const _) (measurable_pi_apply i)))))
  · simp [hS]

def decision (q r0 s : ℕ) (x : Sample I) : Bool :=
  if observedScores r0 s x ∈ acceptSet q then true else false

lemma decision_iff (q r0 s : ℕ) (x : Sample I) :
    decision q r0 s x=true ↔ stageAccept q r0 s x := by
  simp [decision,observedScores,acceptSet,stageAccept,accepts,Certified]

lemma decision_adapted (q r0 : ℕ) : Adapted (scoreFiltration (I:=I) r0) (decision q r0) := by
  intro s
  have hm : Measurable[scoreFiltration r0 s] (observedScores (I:=I) r0 s) :=
    (Filtration.stronglyAdapted_natural (fun s => (observedScores_measurable (I:=I) r0 s).stronglyMeasurable) s).measurable
  exact Measurable.ite (hm (acceptSet_measurable q)) measurable_const measurable_const

/-- No future observations beyond the current end-of-block prefix are used. -/
theorem observedScores_prefix (r0 s : ℕ) (x y : Sample I)
    (h : ∀ i k,k < repetitions r0 s → ∀ a : Fin 4,x i (k,a)=y i (k,a)) :
    observedScores r0 s x=observedScores r0 s y := by
  funext i
  unfold observedScores score CIGAMF.P13.D6DiscoveryPathLaw.average
  congr 1
  apply sum_congr rfl
  intro t ht
  rw [h i t.1.val t.1.isLt t.2]

def first (q r0 : ℕ) : Sample I → WithTop ℕ := hittingAfter (decision q r0) {true} 0

/-- Exact observable stopping event, with certificates checked at completed blocks. -/
theorem first_le_iff (q r0 N : ℕ) (x : Sample I) :
    first q r0 x ≤ N ↔ ∃ s ≤ N,stageAccept q r0 s x := by
  unfold first
  constructor
  · intro h
    obtain ⟨s,hs,ha⟩ := (hittingAfter_le_iff (u:=decision (I:=I) q r0)
      (s:={true}) (n:=0) (i:=N) (ω:=x)).mp h
    exact ⟨s,hs.2,(decision_iff q r0 s x).mp ha⟩
  · rintro ⟨s,hs,ha⟩
    apply (hittingAfter_le_iff (u:=decision (I:=I) q r0)
      (s:={true}) (n:=0) (i:=N) (ω:=x)).mpr
    exact ⟨s,⟨Nat.zero_le _,hs⟩,(decision_iff q r0 s x).mpr ha⟩

theorem first_isStoppingTime (q r0 : ℕ) : IsStoppingTime (scoreFiltration (I:=I) r0) (first q r0) :=
  (decision_adapted q r0).isStoppingTime_hittingAfter (measurableSet_singleton true)

/-- Almost-sure termination uses the actual Gaussian concentration theorem,
not a high-probability correctness event alone. -/
theorem first_terminates (means : I → Fin 4 → ℝ) (B : Finset I) (a : I)
    (hm : ∀ i,(∑ t,CIGAMF.P13.D6NuisanceFreeDiscoveryLaw.signs t*means i t)=target B a i)
    (r0 : ℕ) (hr0 : 512 ≤ r0) :
    ∀ᵐ x ∂vectorPath means,first B.card r0 x < ⊤ := by
  filter_upwards [discovery_terminates means B a hm r0 hr0] with x hx
  obtain ⟨s,hs⟩ := hx
  exact lt_of_le_of_lt ((first_le_iff B.card r0 s x).mpr ⟨s,le_rfl,hs⟩) (by simp)

/-- The existing queryCost is exactly the raw-query count at first acceptance. -/
theorem cost_at_first (q r0 s : ℕ) (x : Sample I) (hs : first q r0 x=(s:WithTop ℕ)) :
    queryCost q r0 x=(4*Fintype.card I*r0:ℕ)*(2:ℝ≥0∞)^s := by
  have hle : first q r0 x ≤ s := by rw [hs]
  obtain ⟨t,ht,hacc⟩ := (first_le_iff q r0 s x).mp hle
  have hst : s ≤ t := by
    have h := (first_le_iff q r0 t x).mpr ⟨t,le_rfl,hacc⟩
    rw [hs] at h
    exact_mod_cast h
  have hts : t=s := by omega
  subst t
  have hb : ∀ t < s,¬ stageAccept q r0 t x := by
    intro t ht ha
    have h := (first_le_iff q r0 t x).mpr ⟨t,le_rfl,ha⟩
    rw [hs] at h
    have : s ≤ t := by exact_mod_cast h
    omega
  unfold queryCost
  rw [work_at_first_accept _ x s hacc hb]

/-- A separate finite-expectation theorem, for the actual raw-query cost. -/
theorem first_expected_cost_finite (means : I → Fin 4 → ℝ) (B : Finset I) (a : I)
    (hm : ∀ i,(∑ t,CIGAMF.P13.D6NuisanceFreeDiscoveryLaw.signs t*means i t)=target B a i)
    (r0 : ℕ) (hr0 : 512 ≤ r0) :
    (∫⁻ x,queryCost B.card r0 x ∂vectorPath means) < ⊤ :=
  discovery_expected_cost_finite means B a hm r0 hr0

#print axioms observedScores_prefix
#print axioms first_le_iff
#print axioms first_isStoppingTime
#print axioms first_terminates
#print axioms cost_at_first
#print axioms first_expected_cost_finite
end
end CIGAMF.P13.D6DiscoveryStoppingTime
