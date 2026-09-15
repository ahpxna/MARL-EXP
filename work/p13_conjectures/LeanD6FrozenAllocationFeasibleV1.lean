import «LeanD6FrozenScalarAllocationV1»

/-! Removes the frozen-design guard and nuisance premises on the whole
margin interval [1/2,1], for every q >= 3 and frozen B-on mass <= 1/4. -/
namespace CIGAMF.P13.D6FrozenAllocationFeasible
open scoped BigOperators
open CIGAMF.P13.D6AllocationPhaseThreeCore CIGAMF.P13.D6FrozenScalarAllocation
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6PhaseThreePrimal CIGAMF.P13.D6AllocationRiskBridge
noncomputable section
variable {n : ℕ}

lemma frozen_coefficients (q w : ℝ) (hq : 3 ≤ q) (hw : 0 ≤ w) (hw1 : w ≤ 1/4) :
    0 < coefficient q w ∧ 0 < p q w ∧ 0 ≤ beta q w ∧ beta q w < p q w ∧
      0 ≤ w*(q-2)/coefficient q w ∧ w*(q-2)/coefficient q w ≤ 1 := by
  have hqp : 0 < q := by linarith
  have hC : 0 < coefficient q w := by
    unfold coefficient
    have h1 : 0 < (1-w)*(q-1)/q := div_pos (mul_pos (by linarith) (by linarith)) hqp
    have h2 : 0 ≤ w*(q-2)^2 := mul_nonneg hw (sq_nonneg _)
    linarith
  have hp : 0 < p q w := div_pos (by linarith) hqp
  have hbeta : 0 ≤ beta q w := by
    unfold beta
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hw) (mul_pos hqp hC).le
  have hpoly : -5 ≤ q*(q-2)^2-q*(q-1)-(q-1) := by
    have h := mul_nonneg (show 0 ≤ q-3 by linarith) (show 0 ≤ q^2-2*q-2 by nlinarith)
    nlinarith only [h]
  have hgap : 0 < coefficient q w-(q-1)*w := by
    have hh := mul_le_mul_of_nonneg_left hpoly hw
    have hid : q*(coefficient q w-(q-1)*w)=
        (q-1)+w*(q*(q-2)^2-q*(q-1)-(q-1)) := by
      unfold coefficient
      field_simp [ne_of_gt hqp]
      <;> ring
    have hpos : 0 < q*(coefficient q w-(q-1)*w) := by nlinarith only [hid,hh,hq,hw1]
    exact pos_of_mul_pos_right hpos hqp.le
  have hbetap : beta q w < p q w := by
    unfold beta p
    apply (div_lt_div_iff₀ (mul_pos hqp hC) hqp).mpr
    have hh := mul_pos (mul_pos (by linarith : 0 < 1-w) hqp) hgap
    nlinarith only [hh]
  have ht0 : 0 ≤ w*(q-2)/coefficient q w := div_nonneg (mul_nonneg hw (by linarith)) hC.le
  have ht1 : w*(q-2)/coefficient q w ≤ 1 := by
    apply (div_le_one hC).mpr
    have h1 : 0 ≤ (1-w)*(q-1)/q := div_nonneg (mul_nonneg (by linarith) (by linarith)) hqp.le
    have h2 : 0 ≤ w*(q-2)*(q-3) := mul_nonneg (mul_nonneg hw (by linarith)) (by linarith)
    unfold coefficient
    nlinarith only [h1,h2]
  exact ⟨hC,hp,hbeta,hbetap,ht0,ht1⟩

/-- The nearest-alternative guard holds and its nuisance stays legal on the
entire half interval; these are no longer external assumptions. -/
theorem frozen_half_interval_conditions (q w mu : ℝ) (hq : 3 ≤ q)
    (hw : 0 ≤ w) (hw1 : w ≤ 1/4) (hm : 1/2 ≤ mu) (hm1 : mu ≤ 1) :
    beta q w*(1-mu)^2 ≤ p q w*mu^2 ∧
      0 ≤ mu-delta q w mu ∧ mu-delta q w mu ≤ 1 := by
  obtain ⟨hc,hp,hb,hbp,ht0,ht1⟩ := frozen_coefficients q w hq hw hw1
  have hsq : (1-mu)^2 ≤ mu^2 := by nlinarith
  have hguard := (mul_le_mul_of_nonneg_left hsq hb).trans
    (mul_le_mul_of_nonneg_right hbp.le (sq_nonneg mu))
  have hd : delta q w mu=(w*(q-2)/coefficient q w)*(1-mu) := by unfold delta; ring
  have hd0 : 0 ≤ delta q w mu := by rw [hd]; exact mul_nonneg ht0 (by linarith)
  have hd1 : delta q w mu ≤ 1-mu := by
    rw [hd]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 (show 0 ≤ 1-mu by linarith)
  exact ⟨hguard,by linarith,by linarith⟩

/-- Exact value for all actual alternatives, with only interval assumptions. -/
theorem frozen_half_interval_value (A : Finset (I n)) (j : I n) (q w mu : ℝ)
    (hq : 3 ≤ q) (hw : 0 ≤ w) (hw1 : w ≤ 1/4)
    (hm : 1/2 ≤ mu) (hm1 : mu ≤ 1) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    allocationValue A j mu (queries A j) (weights A j q w)=D6FrozenScalarAllocation.value q w mu := by
  have hc := frozen_coefficients q w hq hw hw1
  have hf := frozen_half_interval_conditions q w mu hq hw hw1 hm hm1
  exact frozen_actual_value A j q w mu hq hw (by linarith) hc.1 hj hA hB hf.1 hf.2.1 hf.2.2

#print axioms frozen_coefficients
#print axioms frozen_half_interval_conditions
#print axioms frozen_half_interval_value
end
end CIGAMF.P13.D6FrozenAllocationFeasible
