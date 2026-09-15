import «LeanD6ActualDiscoveryBridgeV1»
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! Revalidation on one raw-query path: r0 fresh contrasts per epoch, and
exponentially growing allocation epochs. The expected total length of epochs
with failed/wrong discovery is finite. This controls erroneous commitments;
it does not by itself prove tracking, allocation regret, or a Gamma rate. -/
namespace CIGAMF.P13.D6RepeatedDiscovery
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6DiscoveryVectorCertificate CIGAMF.P13.D6DiscoveryStopping
open CIGAMF.P13.D6NuisanceFreeDiscoveryLaw
open CIGAMF.P13.D6ActualDiscoveryBridge
noncomputable section
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

def epochSamples (r0 s : ℕ) := r0*(s+1)

def badEpochWork (B : Finset J) (a : J) (r0 : ℕ) (x : Sample J) : ℝ≥0∞ :=
  ∑' s : ℕ,(bad B a (epochSamples r0 s)).indicator (fun _ => (2:ℝ≥0∞)^s) x

lemma bad_measurable (B : Finset J) (a : J) (r : ℕ) : MeasurableSet (bad B a r) := by
  simp only [bad,Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun i => measurableSet_le measurable_const
    (((score_measurable r i).sub_const _).abs))

lemma linear_exp_bound (r0 s : ℕ) (hr0 : 512 ≤ r0) :
    Real.exp (-(epochSamples r0 s:ℝ)/128) ≤ Real.exp (-(r0:ℝ)/128)*(1/4:ℝ)^s := by
  have hr : (512:ℝ) ≤ r0 := by exact_mod_cast hr0
  have he : Real.exp (-(r0:ℝ)/128) ≤ (1:ℝ)/4 := by
    rw [show -(r0:ℝ)/128 = -((r0:ℝ)/128) by ring,Real.exp_neg]
    have hh : (4:ℝ) ≤ Real.exp ((r0:ℝ)/128) := by
      have ht := Real.add_one_le_exp ((r0:ℝ)/128);linarith
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) hh
  have hid : -(epochSamples r0 s:ℝ)/128=(s+1:ℕ)*(-(r0:ℝ)/128) := by
    simp only [epochSamples,Nat.cast_mul,Nat.cast_add,Nat.cast_one];ring
  rw [hid,Real.exp_nat_mul,pow_succ,mul_comm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_nonneg _) he s) (Real.exp_nonneg _)

lemma epoch_tail (m : J → Fin 4 → ℝ) (B : Finset J) (a : J)
    (hm : ∀ i,(∑ t,signs t*m i t)=target B a i)
    (r0 : ℕ) (hr0 : 512 ≤ r0) (s : ℕ) :
    vectorPath m (bad B a (epochSamples r0 s)) ≤ eta (Fintype.card J) r0*(4⁻¹:ℝ≥0∞)^s := by
  have hh := vector_tail m B a hm (epochSamples r0 s) (Nat.mul_pos (by omega) (by omega))
  have hd := mul_le_mul_of_nonneg_left (linear_exp_bound r0 s hr0)
    (by positivity : 0 ≤ 2*(Fintype.card J:ℝ))
  have he := ENNReal.ofReal_le_ofReal (hh.trans hd)
  rw [ofReal_measureReal] at he
  have heq : ENNReal.ofReal (2*(Fintype.card J:ℝ)*(Real.exp (-(r0:ℝ)/128)*(1/4:ℝ)^s)) =
      eta (Fintype.card J) r0*(4⁻¹:ℝ≥0∞)^s := by
    rw [← mul_assoc,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num)]
    simp [eta]
  rwa [heq] at he

/-- Cost weighted by whole future epoch lengths, so one early wrong label is
not charged as merely one failed query. No independence across epochs is used. -/
theorem expected_bad_epoch_work (m : J → Fin 4 → ℝ) (B : Finset J) (a : J)
    (hm : ∀ i,(∑ t,signs t*m i t)=target B a i) (r0 : ℕ) (hr0 : 512 ≤ r0) :
    (∫⁻ x,badEpochWork B a r0 x ∂vectorPath m) ≤ 2*eta (Fintype.card J) r0 := by
  unfold badEpochWork
  rw [lintegral_tsum (fun s => (measurable_const.indicator (bad_measurable B a _)).aemeasurable)]
  calc
    _ = ∑' s : ℕ,(2:ℝ≥0∞)^s*vectorPath m (bad B a (epochSamples r0 s)) := by
      apply tsum_congr;intro s
      exact lintegral_indicator_const (bad_measurable B a _) _
    _ ≤ ∑' s : ℕ,(2:ℝ≥0∞)^s*(eta (Fintype.card J) r0*(4⁻¹:ℝ≥0∞)^s) :=
      ENNReal.tsum_le_tsum (fun s => mul_le_mul le_rfl (epoch_tail m B a hm r0 hr0 s) (by positivity) (by positivity))
    _ = eta (Fintype.card J) r0*∑' s : ℕ,(2⁻¹:ℝ≥0∞)^s := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr;intro s
      have he : (2:ℝ≥0∞)*4⁻¹=2⁻¹ := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num
      calc
        _ = eta (Fintype.card J) r0*((2:ℝ≥0∞)^s*(4⁻¹:ℝ≥0∞)^s) := by ac_rfl
        _ = _ := by rw [← mul_pow,he]
    _ = _ := by rw [ENNReal.tsum_geometric_two,mul_comm]

/-- Rechecking yields eventual correct certification almost surely, including
paths that previously certified a wrong label. -/
theorem eventually_correct (m : J → Fin 4 → ℝ) (B : Finset J) (a : J)
    (hm : ∀ i,(∑ t,signs t*m i t)=target B a i) (r0 : ℕ) (hr0 : 512 ≤ r0) :
    ∀ᵐ x ∂vectorPath m, ∀ᶠ s in Filter.atTop,
      accepts (epochSamples r0 s) B.card x ∧
      ∀ S, Certified (epochSamples r0 s) B.card x S → S=B := by
  have hs : (∑' s : ℕ,vectorPath m (bad B a (epochSamples r0 s))) ≠ ∞ := by
    apply ne_top_of_le_ne_top (b := eta (Fintype.card J) r0*2) (by dsimp [eta];finiteness)
    calc
      _ ≤ ∑' s : ℕ,eta (Fintype.card J) r0*(2⁻¹:ℝ≥0∞)^s :=
        ENNReal.tsum_le_tsum (fun s => (epoch_tail m B a hm r0 hr0 s).trans (by
          have he : (4⁻¹:ℝ≥0∞) ≤ 2⁻¹ := by exact ENNReal.inv_le_inv.mpr (by norm_num)
          gcongr))
      _ = _ := by rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric_two]
  filter_upwards [ae_eventually_notMem hs] with x hx
  filter_upwards [hx] with s hs
  exact ⟨good_accepts B a _ x hs,fun S hS => good_certificate_correct B S a _ x hs hS⟩

/-- The recommendation uses only observations and the known cardinality q.
When no certificate exists it returns an explicit fallback and is checked anew
at the next epoch; that fallback's entire epoch is included in the loss bound. -/
def recommendation (q r : ℕ) (x : Sample J) : Finset J :=
  if h : accepts r q x then Classical.choose h else ∅

lemma recommendation_correct_on_good (B : Finset J) (a : J) (r : ℕ) (x : Sample J)
    (hx : x ∉ bad B a r) : recommendation B.card r x=B := by
  have ha := good_accepts B a r x hx
  rw [recommendation,dif_pos ha]
  exact good_certificate_correct B _ a r x hx (Classical.choose_spec ha)

def wrongEpochWork (B : Finset J) (r0 : ℕ) (x : Sample J) : ℝ≥0∞ :=
  ∑' s : ℕ,{y | recommendation B.card (epochSamples r0 s) y ≠ B}.indicator
    (fun _ => (2:ℝ≥0∞)^s) x

theorem wrong_epoch_work_le (B : Finset J) (a : J) (r0 : ℕ) (x : Sample J) :
    wrongEpochWork B r0 x ≤ badEpochWork B a r0 x := by
  apply ENNReal.tsum_le_tsum
  intro s
  by_cases hb : x ∈ bad B a (epochSamples r0 s)
  · rw [Set.indicator_of_mem hb]
    by_cases hw : x ∈ {y | recommendation B.card (epochSamples r0 s) y ≠ B}
    · simp only [Set.indicator_of_mem hw,le_refl]
    · simp only [Set.indicator_of_notMem hw];exact zero_le
  · have hc := recommendation_correct_on_good B a _ x hb
    simp [Set.indicator_of_notMem hb,hc]

theorem expected_wrong_epoch_work (m : J → Fin 4 → ℝ) (B : Finset J) (a : J)
    (hm : ∀ i,(∑ t,signs t*m i t)=target B a i) (r0 : ℕ) (hr0 : 512 ≤ r0) :
    (∫⁻ x,wrongEpochWork B r0 x ∂vectorPath m) ≤ 2*eta (Fintype.card J) r0 :=
  (lintegral_mono (wrong_epoch_work_le B a r0)).trans (expected_bad_epoch_work m B a hm r0 hr0)

/-- Actual D6 query means discharge the only generic mean premise. -/
theorem actual_expected_bad_epoch_work {n : ℕ} (A : Finset (CIGAMF.P13.D6Threshold.I n))
    (j : CIGAMF.P13.D6Threshold.I n) (hj : j ∉ A) (a : Off j) (helper : Off j → Off j)
    (ha : ∀ i,a ≠ helper i) (hi : ∀ i,i ≠ helper i) (mu : ℝ)
    (r0 : ℕ) (hr0 : 512 ≤ r0) :
    (∫⁻ x,badEpochWork (encodedB A j) a r0 x ∂vectorPath (means A j a helper mu)) ≤
      2*eta (Fintype.card (Off j)) r0 :=
  expected_bad_epoch_work _ _ a (actual_mean_identity A j hj a helper ha hi mu) r0 hr0

#print axioms epoch_tail
#print axioms expected_bad_epoch_work
#print axioms eventually_correct
#print axioms expected_wrong_epoch_work
#print axioms actual_expected_bad_epoch_work
end
end CIGAMF.P13.D6RepeatedDiscovery
