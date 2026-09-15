import «LeanAdaptivePathAbsorptionV1»
import «LeanD6AnytimeFrozenCertificateV1»

/-! Anytime label and literal support-geometry correctness on the canonical
actual adaptive path. Finite marginals and almost-sure absorption are proved.
Absorption is required only of the algorithm's update function, not of every
possible sequence of states. The record and certificate premises are explicit.
This module does not assert termination or an expected-sample Gamma rate. -/
namespace CIGAMF.P13.D6AnytimePathBridge
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.AdaptiveTranscriptKernel CIGAMF.P13.AdaptivePathLaw
open CIGAMF.P13.AdaptivePathAbsorption
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AdaptiveTranscript
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6GaussianQueryDominance
open CIGAMF.P13.D6FrozenMixtureCertificate CIGAMF.P13.D6StoppingGeometryBridge
open CIGAMF.P13.D6AnytimeFrozenCertificate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {H : Type*} [MeasurableSpace H]

instance actualStepMarkov (m : H → ℝ) (hm : Measurable m)
    (update : H × ℝ → H) (hu : Measurable update) :
    IsMarkovKernel (actualStep m hm update hu) := by
  unfold actualStep
  exact Kernel.IsMarkovKernel.map _ hu

abbrev adaptivePath (A : Finset (I n)) (j : I n) (mu : ℝ)
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (policy : ℕ → H → Measurement n)
    (hm : ∀ t,Measurable (fun h => actualMean A j mu (policy t h)))
    (update : ℕ → H × ℝ → H) (hu : ∀ t,Measurable (update t)) :
    Measure (ℕ → H) := path (initial ())
      (fun t => actualStep (fun h => actualMean A j mu (policy t h)) (hm t) (update t) (hu t))

lemma actualStep_preserves_bad (m : H → ℝ) (hm : Measurable m)
    (update : H × ℝ → H) (hu : Measurable update)
    (bad : Set H) (hbad : MeasurableSet bad) (h : H)
    (preserve : ∀ y,update (h,y) ∈ bad) :
    ∀ᵐ h' ∂actualStep m hm update hu h,h' ∈ bad := by
  rw [actualStep_apply]
  exact (ae_map_iff (hu.comp (measurable_const.prodMk measurable_id)).aemeasurable hbad).mpr
    (Filter.Eventually.of_forall preserve)

/-- Uniform anytime correctness follows from the frozen-record certificate
and a local update invariant, on the actual infinite adaptive transcript. -/
theorem anytime_label_error_on_path
    (r : ℕ) (j : I (2*r+1))
    (A : Finset (I (2*r+1))) (mu : ℝ) (hworld : A ∈ worlds r j)
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (record : H → List (Measurement (2*r+1) × ℝ)) (policy : ℕ → H → Measurement (2*r+1))
    (hm : ∀ t,Measurable (fun h => actualMean A j mu (policy t h)))
    (stopped : H → Prop) (update : ℕ → H × ℝ → H) (hu : ∀ t,Measurable (update t))
    (hrecord : ∀ t h y,record (update t (h,y))=
      if stopped h then record h else (policy t h,y)::record h)
    (hempty : ∀ᵐ h ∂initial (),record h=[])
    (htrue : Measurable (fun h => logLikelihood A j mu (record h)))
    (prior : Measure ℝ) [IsProbabilityMeasure prior] (W : Finset (Finset (I (2*r+1))))
    (hcandidate : ∀ B ∈ W,Measurable (fun x : H × ℝ => logLikelihood B j x.2 (record x.1)))
    (answer : H → Finset (I (2*r+1))) (hA : A ∈ W) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (delta : ENNReal) (hd : delta ≠ 0) (hdt : delta ≠ ⊤)
    (hcert : ∀ h,stopped h → Certificate prior W j (record h) (answer h) ((W.card:ENNReal)/delta))
    (hbad : MeasurableSet {h | stopped h ∧ answer h ≠ A})
    (absorb : ∀ t h y,stopped h →
      stopped (update t (h,y)) ∧ answer (update t (h,y))=answer h) :
    adaptivePath A j mu initial policy hm update hu
      {omega | ∃ N,stopped (omega N) ∧ answer (omega N) ≠ A} ≤ delta := by
  apply anytime_from_actual_marginals initial _ {h | stopped h ∧ answer h ≠ A} hbad ?_ delta ?_
  · intro t h hb
    apply actualStep_preserves_bad _ (hm t) (update t) (hu t) _ hbad h
    intro y
    have hh := absorb t h y hb.1
    exact ⟨hh.1,by rw [hh.2]; exact hb.2⟩
  · intro N
    have hc := delta_calibration W ⟨A,hA⟩ delta hd hdt
    have hh := actual_frozen_label_error A j mu initial record policy hm stopped update hu
      hrecord hempty htrue prior W hcandidate answer hA hmu hmu1
      ((W.card:ENNReal)/delta) hc.1 hc.2.1 hcert N
    rwa [hc.2.2] at hh

set_option maxHeartbeats 400000 in
/-- The same bound for the construction's literal support-geometric output. -/
theorem anytime_geometric_error_on_path
    (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (A : Finset (I (2*r+1))) (mu : ℝ) (hworld : A ∈ worlds r j)
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (record : H → List (Measurement (2*r+1) × ℝ)) (policy : ℕ → H → Measurement (2*r+1))
    (hm : ∀ t,Measurable (fun h => actualMean A j mu (policy t h)))
    (stopped : H → Prop) (update : ℕ → H × ℝ → H) (hu : ∀ t,Measurable (update t))
    (hrecord : ∀ t h y,record (update t (h,y))=
      if stopped h then record h else (policy t h,y)::record h)
    (hempty : ∀ᵐ h ∂initial (),record h=[])
    (htrue : Measurable (fun h => logLikelihood A j mu (record h)))
    (prior : Measure ℝ) [IsProbabilityMeasure prior] (W : Finset (Finset (I (2*r+1))))
    (hcandidate : ∀ B ∈ W,Measurable (fun x : H × ℝ => logLikelihood B j x.2 (record x.1)))
    (answer : H → Finset (I (2*r+1))) (hA : A ∈ W) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (delta : ENNReal) (hd : delta ≠ 0) (hdt : delta ≠ ⊤)
    (hcert : ∀ h,stopped h → Certificate prior W j (record h) (answer h) ((W.card:ENNReal)/delta))
    (hbad : MeasurableSet {h | stopped h ∧ answer h ≠ A})
    (absorb : ∀ t h y,stopped h →
      stopped (update t (h,y)) ∧ answer (update t (h,y))=answer h) :
    adaptivePath A j mu initial policy hm update hu
      {omega | ∃ N,stopped (omega N) ∧ ¬GeometricOptimal A (answer (omega N))ᶜ j mu} ≤ delta := by
  exact (anytime_geometric_event_le (adaptivePath A j mu initial policy hm update hu)
    (fun N (omega : ℕ → H) => omega N) r j hr A hworld mu hmu hmu1 stopped answer).trans
      (anytime_label_error_on_path r j A mu hworld initial record policy hm stopped update hu
        hrecord hempty htrue prior W hcandidate answer hA hmu hmu1 delta hd hdt hcert hbad absorb)

#print axioms actualStepMarkov
#print axioms actualStep_preserves_bad
#print axioms anytime_label_error_on_path
#print axioms anytime_geometric_error_on_path
end
end CIGAMF.P13.D6AnytimePathBridge
