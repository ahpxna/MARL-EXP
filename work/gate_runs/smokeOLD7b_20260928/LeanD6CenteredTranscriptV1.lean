import «LeanD6AdaptiveTranscriptV1»

/-! A margin-independent recentering of the actual B-off product experiment.
Both local margins are represented by Gaussian means ± q epsilon. -/
namespace CIGAMF.P13.D6CenteredTranscript
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.AdaptiveTranscriptKernel CIGAMF.P13.AdaptiveResourceMap
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6AdaptiveTranscript
noncomputable section
variable {n : ℕ} {H : Type*} [MeasurableSpace H]

def recenter (q mu0 : ℝ) : Kernel ℝ ℝ :=
  Kernel.deterministic (fun x => (1+q-q*mu0)-x) (by fun_prop)

instance recenterMarkov (q mu0 : ℝ) : IsMarkovKernel (recenter q mu0) := by
  unfold recenter
  infer_instance

lemma recenter_law (q mu0 mu : ℝ) :
    recenter q mu0 ∘ₘ gaussianReal (q*(mu-mu0)) 1=gaussianReal (1+q-q*mu) 1 := by
  rw [recenter,Measure.deterministic_comp_eq_map,gaussianReal_map_const_sub]
  congr 1
  ring

/-- The full actual adaptive transcript is a single Markov image of the
centered Gaussian sample resource, uniformly over all true margins. -/
theorem centered_transcript
    (A : Finset (I n)) (j : I n) (q mu0 : ℝ) (hq : 2 ≤ q) (hj : j ∉ A)
    (hB : ((others A j).card : ℝ)=q)
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (policy : ℕ → H → Measurement n) (legal : ∀ t h, Legal j q (policy t h))
    (ha : ∀ t, Measurable (fun h => meanOffset A j (policy t h)))
    (hb : ∀ t, Measurable (fun h => meanSlope A j (policy t h)))
    (update : ℕ → H × ℝ → H) (hu : ∀ t, Measurable (update t)) (N : ℕ) :
    ∃ hm : ∀ mu t, Measurable (fun h => actualMean A j mu (policy t h)),
      ∃ K : Kernel (Samples ℝ N) H, IsMarkovKernel K ∧ ∀ mu,
        K ∘ₖ resource (gaussianReal (q*(mu-mu0)) 1) N =
          trajectory initial (fun t => actualStep (fun h => actualMean A j mu (policy t h))
            (hm mu t) (update t) (hu t)) N := by
  obtain ⟨hm,K,hK,h⟩ := actual_Boff_transcript A j q hq hj hB initial policy legal ha hb update hu N
  letI := hK
  refine ⟨hm,?_⟩
  apply remove_ancillary (recenter q mu0) (fun mu => gaussianReal (q*(mu-mu0)) 1) N K _
  intro mu
  rw [recenter_law]
  exact h mu

#print axioms recenter_law
#print axioms centered_transcript
end
end CIGAMF.P13.D6CenteredTranscript
