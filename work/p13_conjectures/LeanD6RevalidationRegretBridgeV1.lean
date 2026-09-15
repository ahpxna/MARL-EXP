import «LeanD6RepeatedDiscoveryV1»
import «LeanD6AdaptiveOracleRegretV1»

/-! The erroneous-label contribution to actual D6 oracle regret is bounded
across all allocation epochs. This is a decomposition term, not a matching
regret theorem: the regret inside correctly labelled epochs remains to prove. -/
namespace CIGAMF.P13.D6RevalidationRegretBridge
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6LocalOracleRegret
open CIGAMF.P13.D6AdaptiveOracleRegret
open CIGAMF.P13.D6DiscoveryVectorCertificate CIGAMF.P13.D6DiscoveryStopping
open CIGAMF.P13.D6ActualDiscoveryBridge CIGAMF.P13.D6RepeatedDiscovery
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def badRegretWork (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (E : Finset (Measurement n)) (w : ℕ → Sample (Off j) → Measurement n → ℝ)
    (r0 : ℕ) (x : Sample (Off j)) : ℝ≥0∞ :=
  ∑' s : ℕ,(2:ℝ≥0∞)^s *
    {y | recommendation (encodedB A j).card (epochSamples r0 s) y ≠ encodedB A j}.indicator
      (fun y => ENNReal.ofReal (oracleRegret A j q mu E (w s y))) x

lemma bad_regret_work_le (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (E : Finset (Measurement n)) (w : ℕ → Sample (Off j) → Measurement n → ℝ)
    (hw : ∀ s x e, e ∈ E → 0 ≤ w s x e) (r0 : ℕ) (x : Sample (Off j)) :
    badRegretWork A j q mu E w r0 x ≤
      ENNReal.ofReal (max 0 (oracleValue A j q mu))*wrongEpochWork (encodedB A j) r0 x := by
  unfold badRegretWork wrongEpochWork
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro s
  by_cases h : x ∈ {y | recommendation (encodedB A j).card (epochSamples r0 s) y ≠ encodedB A j}
  · simp only [Set.indicator_of_mem h]
    have he := ENNReal.ofReal_le_ofReal (oracle_regret_bounded A j q mu E (w s x) (hw s x))
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left he (show (0:ℝ≥0∞) ≤ 2^s from zero_le)
  · simp only [Set.indicator_of_notMem h,mul_zero,le_refl]

/-- Expected total oracle regret incurred during incorrectly labelled epochs
of lengths 2^s is finite and <= 2*eta*oracleValue. Multiplying epoch lengths by a
fixed raw-query block cost multiplies both sides by the same constant. -/
theorem actual_bad_regret_expectation (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (a : Off j) (helper : Off j → Off j)
    (ha : ∀ i,a ≠ helper i) (hi : ∀ i,i ≠ helper i) (q mu : ℝ)
    (E : Finset (Measurement n)) (w : ℕ → Sample (Off j) → Measurement n → ℝ)
    (hw : ∀ s x e,e ∈ E → 0 ≤ w s x e) (r0 : ℕ) (hr0 : 512 ≤ r0) :
    (∫⁻ x,badRegretWork A j q mu E w r0 x ∂vectorPath (means A j a helper mu)) ≤
      ENNReal.ofReal (max 0 (oracleValue A j q mu))*(2*eta (Fintype.card (Off j)) r0) := by
  have hh := expected_wrong_epoch_work (means A j a helper mu) (encodedB A j) a
    (actual_mean_identity A j hj a helper ha hi mu) r0 hr0
  calc
    _ ≤ ∫⁻ x,ENNReal.ofReal (max 0 (oracleValue A j q mu))*wrongEpochWork (encodedB A j) r0 x
        ∂vectorPath (means A j a helper mu) := lintegral_mono (bad_regret_work_le A j q mu E w hw r0)
    _ = ENNReal.ofReal (max 0 (oracleValue A j q mu)) *
        ∫⁻ x,wrongEpochWork (encodedB A j) r0 x ∂vectorPath (means A j a helper mu) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul le_rfl hh (by positivity) (by positivity)

#print axioms bad_regret_work_le
#print axioms actual_bad_regret_expectation
end
end CIGAMF.P13.D6RevalidationRegretBridge
