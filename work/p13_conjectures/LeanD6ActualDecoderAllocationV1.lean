import «LeanD6DiscoveryWorldRecommendationV1»
import «LeanD6FiniteSolverExpectationV1»

/-! Instantiation with the observation-only D6 decoder, rechecked after r0(s+1)
contrasts. Wrong labels are charged for every query of a 2^s deployment epoch.
The margin estimator still has to be specified separately by the acquisition
schedule; this module does not claim a Gamma stopping rate. -/
namespace CIGAMF.P13.D6ActualDecoderAllocation
open scoped BigOperators ENNReal
open Finset MeasureTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6ActualDiscoveryBridge CIGAMF.P13.D6DiscoveryWorldRecommendation
open CIGAMF.P13.D6DiscoveryVectorCertificate CIGAMF.P13.D6DiscoveryStopping
open CIGAMF.P13.D6RepeatedDiscovery CIGAMF.P13.D6AdaptiveLabelAccounting
open CIGAMF.P13.D6FiniteSolverMeasurability CIGAMF.P13.D6FiniteSolverExpectation
noncomputable section
attribute [local instance] Classical.propDecidable

def decodedWorld (q : ℕ) (j : I (2*q+1)) (fallback : worlds q j)
    (r : ℕ) (x : Sample (Off j)) : worlds q j :=
  ⟨candidate q j fallback.val r x,candidate_valid q j fallback.val fallback.property r x⟩

theorem decodedWorld_measurable (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (fallback : worlds q j) (r : ℕ) : Measurable (decodedWorld q j fallback r) := by
  have hm : Measurable (candidate q j fallback.val r) := by
    apply measurable_to_countable'
    intro W
    exact candidate_level_measurable q hq j fallback.val W r
  exact hm.subtype_mk

/-- Changing any observation after the acquired prefix cannot change the label. -/
theorem decodedWorld_prefix (q : ℕ) (j : I (2*q+1)) (fallback : worlds q j)
    (r : ℕ) (x y : Sample (Off j))
    (h : ∀ i k,k < r → ∀ a : Fin 4,x i (k,a)=y i (k,a)) :
    decodedWorld q j fallback r x=decodedWorld q j fallback r y := by
  have hs : score r x=score r y := by
    funext i
    unfold score CIGAMF.P13.D6DiscoveryPathLaw.average
    congr 1
    apply sum_congr rfl
    intro t ht
    rw [h i t.1.val t.1.isLt t.2]
  apply Subtype.ext
  change candidate q j fallback.val r x=candidate q j fallback.val r y
  have hr : recommendation q r x=recommendation q r y := by
    apply (CIGAMF.P13.D6RecommendationMeasurability.recommendation_eq_iff r q x _).mpr
    have hh := (CIGAMF.P13.D6RecommendationMeasurability.recommendation_eq_iff r q y
      (recommendation q r y)).mp rfl
    simpa only [accepts,Certified,hs] using hh
  unfold candidate
  simp only [hr]

/-- The event is evaluated under the actual legal-query Gaussian means. -/
theorem actual_decoder_tail (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (A : Finset (I (2*q+1))) (hA : A ∈ worlds q j) (fallback : worlds q j)
    (a : Off j) (helper : Off j → Off j) (ha : ∀ i,a ≠ helper i)
    (hi : ∀ i,i ≠ helper i) (mu : ℝ) (r0 : ℕ) (hr0 : 512 ≤ r0) (s : ℕ) :
    vectorPath (means A j a helper mu)
      {x | (decodedWorld q j fallback (epochSamples r0 s) x).val ≠ A} ≤
        eta (Fintype.card (Off j)) r0*(4⁻¹:ℝ≥0∞)^s := by
  have hsub : {x | (decodedWorld q j fallback (epochSamples r0 s) x).val ≠ A} ⊆
      bad (encodedB A j) a (epochSamples r0 s) := by
    intro x hx
    by_contra hg
    exact hx (candidate_correct_on_good q hq j fallback.val A hA a _ x hg)
  exact (measure_mono hsub).trans (epoch_tail _ _ a
    (actual_mean_identity A j (world_parameters q j (by omega) hA).1 a helper ha hi mu)
    r0 hr0 s)

/-- Full deployment-length multiplication, without independence between epochs. -/
theorem actual_wrong_deployment_loss (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (A : Finset (I (2*q+1))) (hA : A ∈ worlds q j) (fallback : worlds q j)
    (a : Off j) (helper : Off j → Off j) (ha : ∀ i,a ≠ helper i)
    (hi : ∀ i,i ≠ helper i) (mu : ℝ) (r0 : ℕ) (hr0 : 512 ≤ r0)
    (C : ℝ≥0∞) (H : ℕ) :
    (∫⁻ x,∑' s : ℕ,{x | (decodedWorld q j fallback (epochSamples r0 s) x).val ≠ A}.indicator
      (fun _ => C*(H:ℝ≥0∞)*(2:ℝ≥0∞)^s) x ∂vectorPath (means A j a helper mu)) ≤
      2*(C*(H:ℝ≥0∞)*eta (Fintype.card (Off j)) r0) := by
  have hb (s : ℕ) : MeasurableSet {x | (decodedWorld q j fallback (epochSamples r0 s) x).val ≠ A} :=
    (measurableSet_eq_fun (measurable_subtype_coe.comp (decodedWorld_measurable q hq j fallback _)) measurable_const).compl
  rw [lintegral_tsum (fun s => (measurable_const.indicator (hb s)).aemeasurable)]
  simp_rw [lintegral_indicator_const (hb _)]
  apply (ENNReal.tsum_le_tsum (fun s => mul_le_mul le_rfl
    (actual_decoder_tail q hq j A hA fallback a helper ha hi mu r0 hr0 s) (by positivity) (by positivity))).trans
  exact le_of_eq (doubling_wrong_label_sum C (eta (Fintype.card (Off j)) r0) H)

/-- For this construction and the required cardinality, safe geometric output
identifies the label exactly; there is no many-label decision shortcut. -/
theorem label_iff_geometry (q : ℕ) (hq : 2 ≤ q) (j : I (2*q+1))
    (A B : worlds q j) (mu : ℝ) (hm : mu ∈ Set.Icc 0 1) :
    CIGAMF.P13.D6StoppingGeometryBridge.GeometricOptimal A.val B.valᶜ j mu ↔ B=A := by
  have hp := world_parameters q j hq A.property
  have hb := world_parameters q j hq B.property
  have hc : B.valᶜ.card=A.val.card := hb.2.2.1.trans (hb.2.1.trans hp.2.1.symm)
  have he := CIGAMF.P13.D6UniqueOptimum.geometric_optimal_iff A.val B.valᶜ j hp.1
    mu hm.1 hm.2 hc hp.2.2.1 hp.2.2.2
  constructor
  · intro h
    exact Subtype.ext (compl_injective (he.mp h))
  · intro h
    apply he.mpr
    rw [h]

/-- Shared-prefix discovery acquisition costs only r0 new contrasts per epoch. -/
theorem discovery_prefix_cost (q r0 s : ℕ) (j : I (2*q+1)) :
    4*Fintype.card (Off j)*epochSamples r0 s=
      4*Fintype.card (Off j)*r0*(s+1) := by unfold epochSamples;ring

#print axioms decodedWorld_measurable
#print axioms decodedWorld_prefix
#print axioms actual_decoder_tail
#print axioms actual_wrong_deployment_loss
#print axioms discovery_prefix_cost
#print axioms label_iff_geometry
end
end CIGAMF.P13.D6ActualDecoderAllocation
