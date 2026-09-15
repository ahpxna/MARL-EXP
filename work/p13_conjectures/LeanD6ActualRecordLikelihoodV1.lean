import «LeanD6AdaptiveMixtureRiskV1»
import «LeanD6StoppingGeometryBridgeV1»

/-! Likelihood computed from the literal adaptive query-response record.
The multiplicative transition is proved, including absorbing records after
a stopping decision. This permits a constant threshold without spending
additional error across observation times. Infinite-path error and expected
stopping time are separate interfaces; no termination claim is made here. -/
namespace CIGAMF.P13.D6ActualRecordLikelihood
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6AdaptiveTranscript
open CIGAMF.P13.D6AdaptiveLikelihood CIGAMF.P13.D6AdaptiveMixtureRisk
open CIGAMF.P13.D6StoppingGeometryBridge CIGAMF.P13.AdaptiveTranscriptKernel
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {H : Type*} [MeasurableSpace H]

def recordRatio (A B : Finset (I n)) (j : I n) (mu nu : ℝ)
    (record : List (Measurement n × ℝ)) : ℝ :=
  Real.exp (logLikelihood B j nu record-logLikelihood A j mu record)

/-- The exact record likelihood increments by the actual Gaussian response
ratio for the adaptively chosen query. -/
theorem record_ratio_cons (A B : Finset (I n)) (j : I n) (mu nu y : ℝ)
    (record : List (Measurement n × ℝ)) (e : Measurement n) :
    recordRatio A B j mu nu ((e,y)::record)=
      recordRatio A B j mu nu record*likelihood (actualMean A j mu e) (actualMean B j nu e) y := by
  unfold recordRatio likelihood logLikelihood
  simp only [List.map_cons,List.sum_cons]
  rw [← Real.exp_add]
  congr 1
  ring

/-- After stopping, retain the record and use likelihood multiplier one.
Before stopping, the complete query-response pair is retained. -/
theorem frozen_record_transition (A B : Finset (I n)) (j : I n) (mu nu : ℝ)
    (record : H → List (Measurement n × ℝ)) (policy : ℕ → H → Measurement n)
    (stopped : H → Prop) (update : ℕ → H × ℝ → H)
    (hrecord : ∀ t h y,record (update t (h,y))=
      if stopped h then record h else (policy t h,y)::record h)
    (t : ℕ) (h : H) (y : ℝ) :
    recordRatio A B j mu nu (record (update t (h,y)))=
      recordRatio A B j mu nu (record h)*likelihood (actualMean A j mu (policy t h))
        (if stopped h then actualMean A j mu (policy t h) else actualMean B j nu (policy t h)) y := by
  rw [hrecord]
  by_cases hs : stopped h
  · simp [hs,likelihood]
  · simpa only [if_neg hs] using record_ratio_cons A B j mu nu y (record h) (policy t h)

theorem actual_record_normalization (A B : Finset (I n)) (j : I n) (mu nu : ℝ)
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (record : H → List (Measurement n × ℝ)) (policy : ℕ → H → Measurement n)
    (hm : ∀ t,Measurable (fun h => actualMean A j mu (policy t h)))
    (stopped : H → Prop) (update : ℕ → H × ℝ → H) (hu : ∀ t,Measurable (update t))
    (hrecord : ∀ t h y,record (update t (h,y))=
      if stopped h then record h else (policy t h,y)::record h)
    (hempty : ∀ᵐ h ∂initial (),record h=[])
    (htrue : Measurable (fun h => logLikelihood A j mu (record h)))
    (hcandidate : Measurable (fun h => logLikelihood B j nu (record h))) (N : ℕ) :
    (∫⁻ h,ENNReal.ofReal (recordRatio A B j mu nu (record h))
      ∂trajectory initial (fun t => actualStep (fun h => actualMean A j mu (policy t h))
        (hm t) (update t) (hu t)) N ())=1 := by
  apply adaptive_likelihood_normalization initial
    (fun t h => actualMean A j mu (policy t h))
    (fun t h => if stopped h then actualMean A j mu (policy t h) else actualMean B j nu (policy t h))
    hm update hu (fun _ h => recordRatio A B j mu nu (record h))
  · intro t
    exact (hcandidate.sub htrue).exp
  · intro t h
    exact (Real.exp_pos _).le
  · calc
      _ = ∫⁻ _h, (1:ENNReal) ∂initial () := by
        apply lintegral_congr_ae
        filter_upwards [hempty] with h hh
        simp [recordRatio,hh,logLikelihood]
      _ = 1 := by simp
  · exact frozen_record_transition A B j mu nu record policy stopped update hrecord

attribute [local irreducible] logLikelihood

set_option maxHeartbeats 400000 in
/-- A uniform finite-horizon bound on the actual stopped record, with the
record recursion discharged. Every candidate and nuisance uses the same
observed adaptive policy. No assumed likelihood normalization remains. -/
theorem actual_frozen_family_tail (A : Finset (I n)) (j : I n) (mu : ℝ)
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
    (c : ENNReal) (hc : c ≠ 0) (hc' : c ≠ ⊤) (N : ℕ) :
    trajectory initial (fun t => actualStep (fun h => actualMean A j mu (policy t h))
      (hm t) (update t) (hu t)) N ()
      {h | ∃ B ∈ W,c ≤ mixture prior (fun nu h => recordRatio A B j mu nu (record h)) h}
      ≤ (W.card:ENNReal)/c := by
  have hstep : ∀ t,IsMarkovKernel
      (actualStep (fun h => actualMean A j mu (policy t h)) (hm t) (update t) (hu t)) := by
    intro t
    unfold actualStep
    exact Kernel.IsMarkovKernel.map _ (hu t)
  have htraj : ∀ t,IsMarkovKernel (trajectory initial
      (fun t => actualStep (fun h => actualMean A j mu (policy t h)) (hm t) (update t) (hu t)) t) := by
    intro t
    induction t with
    | zero => exact inferInstanceAs (IsMarkovKernel initial)
    | succ t ih =>
      letI := ih
      letI := hstep t
      change IsMarkovKernel (_ ∘ₖ _)
      infer_instance
  letI := htraj N
  apply finite_family_tail _ prior W (fun B nu h => recordRatio A B j mu nu (record h)) ?_ ?_ c hc hc'
  · intro B hB
    exact ((hcandidate B hB).sub (htrue.comp measurable_fst)).exp
  · intro B hB nu
    have hnu : Measurable (fun h => logLikelihood B j nu (record h)) :=
      Measurable.of_uncurry_right (f := fun h u => logLikelihood B j u (record h))
        (y := nu) (hcandidate B hB)
    exact actual_record_normalization A B j mu nu initial record policy hm stopped update hu
      hrecord hempty htrue hnu N

#print axioms record_ratio_cons
#print axioms frozen_record_transition
#print axioms actual_record_normalization
#print axioms actual_frozen_family_tail
end
end CIGAMF.P13.D6ActualRecordLikelihood
