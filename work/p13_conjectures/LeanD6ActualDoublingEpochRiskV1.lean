import «LeanD6ActualMultiEpochRiskV1»
import «LeanD6EpochBudgetArithmeticV1»

/-! Actual length-weighted finite multi-epoch risk, with shared discovery and
fresh cyclic observations. O(E) refers to recommendation loss only. A pilot
block is acquired before deploying the recommendation; acquisition regret,
tracking, unknown phase and Gamma stopping are not hidden in this statement. -/
namespace CIGAMF.P13.D6ActualDoublingEpochRisk
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6LocalOracleRegret CIGAMF.P13.D6UniformPhaseThreeRemainder
open CIGAMF.P13.D6ActualDiscoveryBridge CIGAMF.P13.D6DiscoveryVectorCertificate
open CIGAMF.P13.D6DiscoveryStopping CIGAMF.P13.D6RepeatedDiscovery
open CIGAMF.P13.D6CyclicPhaseLaw CIGAMF.P13.D6ActualUnknownLabelPhaseRisk
open CIGAMF.P13.D6EpochMarginalLaw CIGAMF.P13.D6ActualMultiEpochRisk
open CIGAMF.P13.D6EpochBudgetArithmetic
noncomputable section

theorem actual_doubling_recommendation_bound (q : ℕ) (hq : 8 ≤ q) (j : I (2*q+1)) :
    ∃ G : ZMod (2*q+1) → Finset (I (2*q+1)),
      (∀ t,Legal j q (.inr (G t,false)) ∧ (G t).card=q) ∧
      ∀ (fallback : Finset (I (2*q+1))) (hf : fallback ∈ worlds q j)
        (a : Off j) (helper : Off j → Off j)
        (ha : ∀ i,a ≠ helper i) (hi : ∀ i,i ≠ helper i)
        (A : Finset (I (2*q+1))) (hA : A ∈ worlds q j)
        (mu : ℝ) (hm : mu ∈ phaseInterval q)
        (r0 : ℕ) (hr0 : 512 ≤ r0) (L0 : ℕ) (hL0 : 0 < L0) (E : ℕ),
      (∫⁻ x,∑ s : Fin E,((L0*2^s.val:ℕ):ℝ≥0∞)*ENNReal.ofReal
        (epochLoss q j fallback A mu (epochSamples r0 s.val) (L0*2^s.val) (epochProj s x))
        ∂multiEpoch (vectorPath (means A j a helper mu))
          (fun s : Fin E => observations G A j mu (L0*2^s.val))) ≤
      (E:ℝ≥0∞)*ENNReal.ofReal (64*((2*q+1:ℕ):ℝ)/(q:ℝ)^6)+
        2*((L0:ℝ≥0∞)*ENNReal.ofReal (max 0 (oracleValue A j q mu))*
          eta (Fintype.card (Off j)) r0) := by
  obtain ⟨G,hG,hbound⟩ := actual_finite_epoch_bound q hq j
  refine ⟨G,hG,?_⟩
  intro fallback hf a helper ha hi A hA mu hm r0 hr0 L0 hL0 E
  have hL : ∀ s : Fin E,0 < L0*2^s.val := fun s => Nat.mul_pos hL0 (by positivity)
  exact (hbound fallback hf a helper ha hi A hA mu hm r0 hr0 E
    (fun s => L0*2^s.val) hL (fun s => ((L0*2^s.val:ℕ):ℝ≥0∞))).trans
      (doubling_recommendation_sum q L0 E (by omega) hL0 _ _)

#print axioms actual_doubling_recommendation_bound
end
end CIGAMF.P13.D6ActualDoublingEpochRisk
