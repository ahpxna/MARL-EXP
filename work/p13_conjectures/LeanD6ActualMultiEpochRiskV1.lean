import «LeanD6EpochMarginalLawV1»
import «LeanD6WeightedEpochCompositionV1»
import «LeanD6GrowingUnknownLabelPhaseRiskV1»
import «LeanD6EpochLossMeasurabilityV1»

/-! Finite-horizon composition on one actual probability space. Discovery
prefixes are shared; cyclic blocks are fresh and A-free. We charge every wrong
recommendation. Weights count uses of the recommendation, not its acquisition
queries. The latter are accounted separately below. This is not a stopping or
Gamma theorem, nor an O(log T) bound on total acquisition regret. -/
namespace CIGAMF.P13.D6ActualMultiEpochRisk
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6LocalOracleRegret CIGAMF.P13.D6UniformPhaseThreeRemainder
open CIGAMF.P13.D6ActualDiscoveryBridge CIGAMF.P13.D6DiscoveryVectorCertificate
open CIGAMF.P13.D6DiscoveryStopping CIGAMF.P13.D6RepeatedDiscovery
open CIGAMF.P13.D6CyclicPhaseLaw CIGAMF.P13.D6ActualUnknownLabelPhaseRisk
open CIGAMF.P13.D6GrowingUnknownLabelPhaseRisk CIGAMF.P13.D6EpochLossMeasurability
open CIGAMF.P13.D6EpochMarginalLaw CIGAMF.P13.D6WeightedEpochComposition
noncomputable section

/-- Actual, history-sharing composition. There is no assumed marginal-law or
conditional-risk premise in this theorem. -/
theorem actual_finite_epoch_bound (q : ℕ) (hq : 8 ≤ q) (j : I (2*q+1)) :
    ∃ G : ZMod (2*q+1) → Finset (I (2*q+1)),
      (∀ t,Legal j q (.inr (G t,false)) ∧ (G t).card=q) ∧
      ∀ (fallback : Finset (I (2*q+1))) (hf : fallback ∈ worlds q j)
        (a : Off j) (helper : Off j → Off j)
        (ha : ∀ i,a ≠ helper i) (hi : ∀ i,i ≠ helper i)
        (A : Finset (I (2*q+1))) (hA : A ∈ worlds q j)
        (mu : ℝ) (hm : mu ∈ phaseInterval q)
        (r0 : ℕ) (hr0 : 512 ≤ r0) (E : ℕ)
        (L : Fin E → ℕ) (hL : ∀ s,0 < L s) (w : Fin E → ℝ≥0∞),
      (∫⁻ x,∑ s : Fin E,w s*ENNReal.ofReal
        (epochLoss q j fallback A mu (epochSamples r0 s.val) (L s) (epochProj s x))
        ∂multiEpoch (vectorPath (means A j a helper mu))
          (fun s => observations G A j mu (L s))) ≤
      ∑ s : Fin E,w s*(ENNReal.ofReal (64/(q:ℝ)^2)*
        ENNReal.ofReal (((2*q+1:ℕ):ℝ)/((L s:ℝ)*(q:ℝ)^4))+
        ENNReal.ofReal (max 0 (oracleValue A j q mu))*
          (eta (Fintype.card (Off j)) r0*(4⁻¹:ℝ≥0∞)^s.val)) := by
  obtain ⟨G,hG,hbound⟩ := actual_unknown_label_explicit_bound q hq j
  refine ⟨G,hG,?_⟩
  intro fallback hf a helper ha hi A hA mu hm r0 hr0 E L hL w
  letI : ∀ s : Fin E,IsProbabilityMeasure (observations G A j mu (L s)) :=
    fun s => by unfold observations; infer_instance
  refine epoch_weighted_le (vectorPath (means A j a helper mu))
    (fun s : Fin E => observations G A j mu (L s)) w
    (fun s y => ENNReal.ofReal (epochLoss q j fallback A mu (epochSamples r0 s.val) (L s) y))
    ?_ univ _ ?_
  · intro s
    exact ENNReal.measurable_ofReal.comp
      (epoch_loss_measurable q (by omega) j fallback A hf hA mu hm _ _)
  · intro s hs
    exact hbound fallback hf a helper ha hi A hA mu hm r0 hr0 s.val (L s) (hL s)

/-- One epoch uses a discovery prefix and an independent cyclic block. Across
E epochs each discovery datum is acquired once, not once per prefix. -/
def acquisitionCost (d r0 E : ℕ) (L : Fin E → ℕ) : ℕ :=
  4*d*r0*E+d*∑ s,L s

/-- Incremental discovery cost telescopes exactly. -/
theorem shared_discovery_cost (d r0 E : ℕ) :
    (∑ _s ∈ range E,4*d*r0)=4*d*r0*E := by simp [mul_comm]

/-- For doubling cyclic blocks the acquisition budget is explicit. It is of
order the final block, even though recommendation loss sums logarithmically. -/
theorem doubling_acquisition_cost (d r0 L0 E : ℕ) :
    4*d*r0*E+d*(∑ s ∈ range E,L0*2^s)=
      4*d*r0*E+d*L0*(2^E-1) := by
  rw [doubling_budget]
  ring

#print axioms actual_finite_epoch_bound
#print axioms shared_discovery_cost
#print axioms doubling_acquisition_cost
end
end CIGAMF.P13.D6ActualMultiEpochRisk
