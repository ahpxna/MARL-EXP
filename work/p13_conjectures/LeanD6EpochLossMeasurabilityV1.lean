import «LeanD6ActualUnknownLabelPhaseRiskV1»
import «LeanD6ConstructiveTrackingV1»

/-! The one-epoch loss is an actual measurable integrable random variable.
This closes the distinction between an unrestricted lower integral and an
expectation for the decoder/cyclic allocation construction. -/
namespace CIGAMF.P13.D6EpochLossMeasurability
open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationRiskBridge CIGAMF.P13.D6LocalOracleRegret
open CIGAMF.P13.D6AllocationTrackingStability CIGAMF.P13.D6ConstructiveTracking
open CIGAMF.P13.D6PhaseThreePrimal CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationPhaseThreeFeasible CIGAMF.P13.D6AllocationMarginRegion
open CIGAMF.P13.D6UniformPhaseThreeRemainder CIGAMF.P13.D6CyclicMeanSquare
open CIGAMF.P13.D6CyclicPhaseLaw CIGAMF.P13.D6ActualDiscoveryBridge
open CIGAMF.P13.D6DiscoveryWorldRecommendation CIGAMF.P13.D6ActualUnknownLabelPhaseRisk
open CIGAMF.P13.D6RandomLabelPhaseRegret CIGAMF.P13.D6AdaptiveOracleRegret
noncomputable section
attribute [local instance] Classical.propDecidable

lemma allocation_value_continuous {T : Type*} [TopologicalSpace T] {n : ℕ}
    (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (halt : ∃ A' nu,Admissible A A' j nu) (q mu : ℝ)
    (hq : 0 ≤ q) (hm : 0 ≤ mu) (hm1 : mu ≤ 1)
    (E : Finset (Measurement n)) (w : T → Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ x e,e ∈ E → 0 ≤ w x e)
    (hc : ∀ e,e ∈ E → Continuous (fun x => w x e)) :
    Continuous (fun x => allocationValue A j mu E (w x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hg : Continuous (fun y => informationCap q*(∑ e ∈ E,|w y e-w x e|)) := by
    apply continuous_const.mul
    exact continuous_finset_sum E (fun e he => ((hc e he).sub continuous_const).abs)
  have ht : Filter.Tendsto (fun y => informationCap q*(∑ e ∈ E,|w y e-w x e|))
      (nhds x) (nhds 0) := by simpa using (hg.continuousAt (x:=x)).tendsto
  apply squeeze_zero (fun y => norm_nonneg _) ?_ ht
  intro y
  simpa only [Real.norm_eq_abs] using
    allocation_l1_modulus A j hj halt q mu hq hm hm1 E (w y) (w x) hl (hw y) (hw x)

lemma clipped_mass_continuous (q : ℝ) (hq : 3 ≤ q)
    (hi : marginMax q ≤ marginHigh q) :
    Continuous (fun x => mass q (clip (marginMax q) (marginHigh q) x)) := by
  have hD : Continuous (D q) := by unfold D radicand;fun_prop
  have hd : ∀ m ∈ phaseInterval q,0 < D q m := by
    intro m hm
    have hb := phase_shift_bounds q m hq hm.1 hm.2
    exact radical_positive q m hq (by linarith [hb.1])
  have hs : ContinuousOn (shift q) (phaseInterval q) := by
    unfold shift
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro m hm
    have hb := phase_shift_bounds q m hq hm.1 hm.2
    have hh : 0 ≤ q*(q-2)*(1-m) := mul_nonneg
      (mul_nonneg (by linarith) (by linarith)) (by linarith [hb.2.1])
    linarith [hd m hm]
  have hc : ContinuousOn (mass q) (phaseInterval q) := by
    unfold mass
    exact (continuousOn_const.mul hs).div hD.continuousOn (fun m hm => ne_of_gt (hd m hm))
  exact hc.comp_continuous (by unfold clip;fun_prop) (fun x => clip_mem _ _ _ hi)

lemma branch_loss_continuous (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (A W : Finset (I (2*q+1))) (hA : A ∈ worlds q j) (hW : W ∈ worlds q j)
    (mu : ℝ) (hm : mu ∈ phaseInterval q) :
    Continuous (fun x => oracleRegret A j q mu (D6PhaseThreePrimal.queries W j)
      (weights W j q (mass q (clip (marginMax q) (marginHigh q) x)))) := by
  have hp := world_parameters q j (by omega) hA
  have hb := phase_shift_bounds q mu (by exact_mod_cast hq) hm.1 hm.2
  have hc := clipped_mass_continuous q (by exact_mod_cast hq) (hm.1.trans hm.2)
  have hw (x : ℝ) := phase_mass_bounds q (clip (marginMax q) (marginHigh q) x)
    (by exact_mod_cast hq) (clip_mem _ _ x (hm.1.trans hm.2)).1
    (clip_mem _ _ x (hm.1.trans hm.2)).2
  have hd (x : ℝ) := distribution W j q (mass q (clip (marginMax q) (marginHigh q) x))
    (by exact_mod_cast (show 0<q by omega)) (hw x).1 (by linarith [(hw x).2])
    (by exact_mod_cast world_others_card q (by omega) j W hW)
  have hv := allocation_value_continuous A j hp.1 (world_has_alternative q j (by omega) A hA)
    q mu (by positivity) (by linarith [hb.1]) hb.2.1 (D6PhaseThreePrimal.queries W j)
    (fun x => weights W j q (mass q (clip (marginMax q) (marginHigh q) x)))
    (hd 0).1 (fun x e _ => (hd x).2.1 e) (by
      intro e he
      unfold weights
      apply Continuous.add
      · split_ifs <;> first | exact hc | exact continuous_const
      · apply continuous_finsetSum
        intro i hi
        split_ifs
        · exact (continuous_const.sub hc).div_const _
        · exact continuous_const)
  unfold oracleRegret
  exact continuous_const.max (continuous_const.sub hv)

theorem epoch_loss_measurable (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (fallback A : Finset (I (2*q+1))) (hf : fallback ∈ worlds q j) (hA : A ∈ worlds q j)
    (mu : ℝ) (hm : mu ∈ phaseInterval q) (r L : ℕ) :
    Measurable (epochLoss q j fallback A mu r L) := by
  let Ω := D6DiscoveryVectorCertificate.Sample (Off j) × (Fin L × ZMod (2*q+1) → ℝ)
  let branch (W : Finset (I (2*q+1))) (x : Ω) :=
    oracleRegret A j q mu (D6PhaseThreePrimal.queries W j)
      (weights W j q (mass q (clip (marginMax q) (marginHigh q)
        (estimate (C:=ZMod (2*q+1)) q L x.2))))
  have hb : ∀ W,W ∈ worlds q j → Measurable (branch W) := by
    intro W hW
    exact (branch_loss_continuous q hq j A W hA hW mu hm).measurable.comp
      (by
        change Measurable (fun x : D6DiscoveryVectorCertificate.Sample (Off j) ×
          (Fin L × ZMod (2*q+1) → ℝ) => estimate (C:=ZMod (2*q+1)) q L x.2)
        unfold estimate
        fun_prop)
  have hs : Measurable (fun x : Ω => ∑ W ∈ worlds q j,
      {y : Ω | candidate q j fallback r y.1=W}.indicator (branch W) x) := by
    apply Finset.measurable_sum
    intro W hW
    exact (hb W hW).indicator ((candidate_level_measurable q hq j fallback W r).preimage measurable_fst)
  convert hs using 1
  funext x
  rw [sum_eq_single (candidate q j fallback r x.1)]
  · simp [epochLoss,branch]
  · intro W hW hne
    exact Set.indicator_of_notMem (by simpa [eq_comm] using hne) _
  · intro h
    exact False.elim (h (candidate_valid q j fallback hf r x.1))

theorem epoch_loss_integrable (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (fallback A : Finset (I (2*q+1))) (hf : fallback ∈ worlds q j) (hA : A ∈ worlds q j)
    (mu : ℝ) (hm : mu ∈ phaseInterval q) (r L : ℕ)
    (P : Measure (D6DiscoveryVectorCertificate.Sample (Off j) × (Fin L × ZMod (2*q+1) → ℝ)))
    [IsFiniteMeasure P] : Integrable (epochLoss q j fallback A mu r L) P := by
  apply (integrable_const (max 0 (oracleValue A j q mu))).mono'
    (epoch_loss_measurable q hq j fallback A hf hA mu hm r L).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hc := candidate_valid q j fallback hf r x.1
  have hz := clip_mem (marginMax q) (marginHigh q)
    (estimate (C:=ZMod (2*q+1)) q L x.2) (hm.1.trans hm.2)
  have hw := phase_mass_bounds q _ (by exact_mod_cast hq) hz.1 hz.2
  have hd := distribution (candidate q j fallback r x.1) j q (mass q _)
    (by exact_mod_cast (show 0<q by omega)) hw.1 (by linarith [hw.2])
    (by exact_mod_cast world_others_card q (by omega) j _ hc)
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ epochLoss q j fallback A mu r L x from le_max_left _ _)]
  exact oracle_regret_bounded A j q mu _ _ (fun e _ => hd.2.1 e)

#print axioms allocation_value_continuous
#print axioms clipped_mass_continuous
#print axioms branch_loss_continuous
#print axioms epoch_loss_measurable
#print axioms epoch_loss_integrable
end
end CIGAMF.P13.D6EpochLossMeasurability
