import «LeanD6FrozenMixtureCertificateV1»
import Mathlib.MeasureTheory.Measure.Continuity

/-! From uniform finite-horizon error to an anytime geometric guarantee on
one path probability space. The path marginals must be the actual adaptive
Gaussian trajectory, and stopping/output must be absorbing. These structural
conditions are explicit; no error bound, termination, or Gamma rate is assumed. -/
namespace CIGAMF.P13.D6AnytimeFrozenCertificate
open MeasureTheory ProbabilityTheory Set
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6AdaptiveTranscript
open CIGAMF.P13.D6FrozenMixtureCertificate CIGAMF.P13.D6StoppingGeometryBridge
open CIGAMF.P13.AdaptiveTranscriptKernel
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

theorem absorbing_event_anytime (P : Measure Ω) (laws : ℕ → Measure H)
    (state : ℕ → Ω → H) (hlaw : ∀ N,HasLaw (state N) (laws N) P)
    (bad : Set H) (hmeas : MeasurableSet bad)
    (absorb : ∀ omega t,state t omega ∈ bad → state (t+1) omega ∈ bad)
    (delta : ENNReal) (hbound : ∀ N,laws N bad ≤ delta) :
    P {omega | ∃ N,state N omega ∈ bad} ≤ delta := by
  have hmono : Monotone (fun N => {omega | state N omega ∈ bad}) := by
    apply monotone_nat_of_le_succ
    intro t omega hw
    exact absorb omega t hw
  have he : {omega | ∃ N,state N omega ∈ bad}=⋃ N,{omega | state N omega ∈ bad} := by
    ext omega
    simp
  rw [he,hmono.measure_iUnion]
  apply iSup_le
  intro N
  have hp := (hlaw N).measure_eq (p := fun h => h ∈ bad) hmeas
  exact hp.le.trans (hbound N)

set_option maxHeartbeats 400000 in
/-- Anytime delta bound for wrong certified labels. Unlike a union bound over
times, the threshold is card(W)/delta with no additional time penalty. -/
theorem actual_anytime_label_error (A : Finset (I n)) (j : I n) (mu : ℝ)
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (record : H → List (Measurement n × ℝ)) (policy : ℕ → H → Measurement n)
    (hm : ∀ t,Measurable (fun h => actualMean A j mu (policy t h)))
    (stopped : H → Prop) (update : ℕ → H × ℝ → H) (hu : ∀ t,Measurable (update t))
    (hrecord : ∀ t h y,record (update t (h,y))=
      if stopped h then record h else (policy t h,y)::record h)
    (hempty : ∀ᵐ h ∂initial (),record h=[])
    (htrue : Measurable (fun h => logLikelihood A j mu (record h)))
    (prior : Measure ℝ) [IsProbabilityMeasure prior] (W : Finset (Finset (I n)))
    (hcandidate : ∀ B ∈ W,Measurable (fun x : H × ℝ => logLikelihood B j x.2 (record x.1)))
    (answer : H → Finset (I n)) (hA : A ∈ W) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (delta : ENNReal) (hd : delta ≠ 0) (hdt : delta ≠ ⊤)
    (hcert : ∀ h,stopped h → Certificate prior W j (record h) (answer h) ((W.card:ENNReal)/delta))
    (P : Measure Ω) (state : ℕ → Ω → H)
    (hlaw : ∀ N,HasLaw (state N) (trajectory initial
      (fun t => actualStep (fun h => actualMean A j mu (policy t h)) (hm t) (update t) (hu t)) N ()) P)
    (hbad : MeasurableSet {h | stopped h ∧ answer h ≠ A})
    (absorb : ∀ omega t,stopped (state t omega) →
      stopped (state (t+1) omega) ∧ answer (state (t+1) omega)=answer (state t omega)) :
    P {omega | ∃ N,stopped (state N omega) ∧ answer (state N omega) ≠ A} ≤ delta := by
  have hc := delta_calibration W ⟨A,hA⟩ delta hd hdt
  apply absorbing_event_anytime P _ state hlaw {h | stopped h ∧ answer h ≠ A} hbad ?_ delta ?_
  · intro omega t hw
    have hh := absorb omega t hw.1
    exact ⟨hh.1,by rw [hh.2]; exact hw.2⟩
  · intro N
    have h := actual_frozen_label_error A j mu initial record policy hm stopped update hu
      hrecord hempty htrue prior W hcandidate answer hA hmu hmu1
      ((W.card:ENNReal)/delta) hc.1 hc.2.1 hcert N
    rwa [hc.2.2] at h

/-- Any wrong support-geometric output implies a wrong label. Together with
actual_anytime_label_error this yields the identical anytime delta bound for
the literal finite-support construction. No stopped output is omitted. -/
theorem anytime_geometric_event_le (P : Measure Ω) (state : ℕ → Ω → H)
    (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r) (A : Finset (I (2*r+1)))
    (hA : A ∈ worlds r j) (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (stopped : H → Prop) (answer : H → Finset (I (2*r+1))) :
    P {omega | ∃ N,stopped (state N omega) ∧ ¬GeometricOptimal A (answer (state N omega))ᶜ j mu} ≤
      P {omega | ∃ N,stopped (state N omega) ∧ answer (state N omega) ≠ A} := by
  apply measure_mono
  rintro omega ⟨N,hs,hbad⟩
  refine ⟨N,hs,?_⟩
  intro he
  apply hbad
  rw [he]
  have hp := D6Threshold.world_parameters r j hr hA
  exact (D6UniqueOptimum.geometric_optimal_iff A Aᶜ j hp.1 mu hmu hmu1
    hp.2.2.1 hp.2.2.1 hp.2.2.2).mpr rfl

set_option maxHeartbeats 400000 in
theorem actual_anytime_geometric_error (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
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
    (P : Measure Ω) (state : ℕ → Ω → H)
    (hlaw : ∀ N,HasLaw (state N) (trajectory initial
      (fun t => actualStep (fun h => actualMean A j mu (policy t h)) (hm t) (update t) (hu t)) N ()) P)
    (hbad : MeasurableSet {h | stopped h ∧ answer h ≠ A})
    (absorb : ∀ omega t,stopped (state t omega) →
      stopped (state (t+1) omega) ∧ answer (state (t+1) omega)=answer (state t omega)) :
    P {omega | ∃ N,stopped (state N omega) ∧ ¬GeometricOptimal A (answer (state N omega))ᶜ j mu} ≤ delta := by
  apply le_trans (anytime_geometric_event_le P state r j hr A hworld mu hmu hmu1 stopped answer)
  exact actual_anytime_label_error A j mu initial record policy hm stopped update hu
    hrecord hempty htrue prior W hcandidate answer hA hmu hmu1 delta hd hdt
    hcert P state hlaw hbad absorb

#print axioms absorbing_event_anytime
#print axioms actual_anytime_label_error
#print axioms anytime_geometric_event_le
#print axioms actual_anytime_geometric_error
end
end CIGAMF.P13.D6AnytimeFrozenCertificate
