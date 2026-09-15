import «LeanD6LocalMatchingDesignV1»
import «LeanGaussianThresholdRiskV1»

/-! Constructive finite-epsilon matching upper bound with known A: take N
actual B-off samples, center them, and choose the two boundary allocations
by the sign of their sum. A fixed boundary design is used on the plus side.
No estimate of the magnitude epsilon is required by this recommendation. -/
namespace CIGAMF.P13.D6KnownLabelMatchingRisk
open MeasureTheory ProbabilityTheory Set
open CIGAMF.P13.AdaptiveTranscriptKernel CIGAMF.P13.D6GaussianOverlap
open CIGAMF.P13.GaussianThresholdDecision CIGAMF.P13.GaussianThresholdRisk
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationMargin
open CIGAMF.P13.D6AllocationPhaseThreeParameters CIGAMF.P13.D6AllocationPhaseThreeFeasible
open CIGAMF.P13.D6AllocationMarginRegion CIGAMF.P13.D6LocalOracleRegret
open CIGAMF.P13.D6FrozenScalarAllocation CIGAMF.P13.D6FrozenAllocationFeasible
open CIGAMF.P13.D6FrozenQuadraticBound CIGAMF.P13.D6LocalMatchingAlgebra
open CIGAMF.P13.D6LocalMatchingDesign
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def minusRisk (A : Finset (I n)) (j : I n) (q mu0 eps : ℝ) (N : ℕ) : ℝ :=
  ∫ x, if choosePlus N x then rightRegret A j q mu0 (mu0-eps) else leftRegret A j q (mu0-eps)
    ∂resource (gaussianReal (-(q*eps)) 1) N ()
def plusRisk (A : Finset (I n)) (j : I n) (q mu0 eps : ℝ) (N : ℕ) : ℝ :=
  ∫ x, if choosePlus N x then rightRegret A j q mu0 (mu0+eps) else leftRegret A j q (mu0+eps)
    ∂resource (gaussianReal (q*eps) 1) N ()

/-- Explicit upper bound with the same leading constant as the adaptive
lower bound, plus a displayed second-order constant. -/
theorem constructive_upper (A : Finset (I n)) (j : I n) (q mu0 eps : ℝ)
    (hq : 3 ≤ q) (hI : Interior q (1-mu0)) (hmI : Interior q (1-(mu0-eps)))
    (h0lo : marginMax q ≤ mu0) (hplushi : mu0+eps ≤ marginHigh q)
    (hminus : 1/2 ≤ mu0-eps) (heps : 0 ≤ eps)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (N : ℕ) (hN : 0 < N) :
    max (minusRisk A j q mu0 eps N) (plusRisk A j q mu0 eps N) ≤
      localJump q mu0*eps*standardTail (q*eps*Real.sqrt N)+
        (remainderConstant q mu0+|localCurvature q mu0|)*eps^2 := by
  have h0hi : mu0 ≤ marginHigh q := by linarith
  have hpluslo : marginMax q ≤ mu0+eps := by linarith
  have h0 := phase_shift_bounds q mu0 hq h0lo h0hi
  have hplus := phase_shift_bounds q (mu0+eps) hq hpluslo hplushi
  have h0lt : mu0 < 1 := by linarith [(D6PhaseThreeDual.phase_nuisance q mu0 hq h0lo h0hi).1]
  have hplt : mu0+eps < 1 := by
    linarith [(D6PhaseThreeDual.phase_nuisance q (mu0+eps) hq hpluslo hplushi).1]
  have hw := phase_mass_bounds q mu0 hq h0lo h0hi
  have hc := frozen_coefficients q (mass q mu0) hq hw.1 hw.2
  have hboundary := boundary_equality A j q mu0 hq hI h0lo h0hi hj hA hB
  have hJ := jump_positive (p q (mass q mu0)) (D6FrozenScalarAllocation.beta q (mass q mu0)) (leftCoefficient q) mu0
    hc.2.1 (by linarith [h0.1]) h0lt hboundary
  have hcoef := hc.1
  have hM : 0 ≤ remainderConstant q mu0 := by unfold remainderConstant; positivity
  have ht : 0 ≤ standardTail (q*eps*Real.sqrt N) := ENNReal.toReal_nonneg
  have ht1 : standardTail (q*eps*Real.sqrt N) ≤ 1 := measureReal_le_one
  have hm := minus_right_loss A j q mu0 (mu0-eps) hq hmI h0lo h0hi hminus
    (by linarith) hj hA hB
  have hright : rightRegret A j q mu0 (mu0+eps) ≤ remainderConstant q mu0*eps^2 := by
    apply actual_frozen_quadratic_regret A j q (mu0+eps) mu0 eps hq hpluslo hplushi
      h0lo h0hi hj hA hB heps
    simp [abs_of_nonneg heps]
  have hr0 : 0 ≤ rightRegret A j q mu0 (mu0+eps) := le_max_left _ _
  have hwrong := plus_left_loss A j q mu0 (mu0+eps) hq hpluslo hplushi h0lo h0hi hplt hj hA hB
  have halg := threshold_pair_upper (p q (mass q mu0)) (D6FrozenScalarAllocation.beta q (mass q mu0)) (leftCoefficient q)
    mu0 eps (standardTail (q*eps*Real.sqrt N))
    (rightRegret A j q mu0 (mu0-eps)) (rightRegret A j q mu0 (mu0+eps))
    (leftRegret A j q (mu0+eps)) (remainderConstant q mu0)
    hboundary heps ht ht1 hJ.le hM hm hr0 hright hwrong
  unfold minusRisk plusRisk
  rw [minus_risk (q*eps) _ _ N hN,plus_risk (q*eps) _ _ N hN,
    left_regret_zero A j q (mu0-eps) hq hmI hj hA hB]
  simpa only [zero_add,sub_zero,localJump,localCurvature] using halg

/-- The exact lower-bound separation dominates J epsilon - epsilon squared.
Combining with the compiled transcript lower bound yields the matching
leading term for every adaptive algorithm. -/
theorem adaptive_separation_leading (A : Finset (I n)) (j : I n) (q mu0 eps : ℝ)
    (hq : 3 ≤ q) (hI : Interior q (1-mu0))
    (h0lo : marginMax q ≤ mu0) (hplushi : mu0+eps ≤ marginHigh q) (heps : 0 ≤ eps)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    localJump q mu0*eps-eps^2 ≤
      rate q (1-(mu0-eps))+D6PhaseThreeSharp.rate q (mu0+eps)-2*rate q (1-mu0)-eps^2 := by
  have h0hi : mu0 ≤ marginHigh q := by linarith
  have hpluslo : marginMax q ≤ mu0+eps := by linarith
  have hw := phase_mass_bounds q mu0 hq h0lo h0hi
  have hc := frozen_coefficients q (mass q mu0) hq hw.1 hw.2
  have hb := boundary_equality A j q mu0 hq hI h0lo h0hi hj hA hB
  have hd := plus_oracle_decomposition A j q mu0 (mu0+eps) hq hpluslo hplushi h0lo h0hi hj hA hB
  have hr : 0 ≤ rightRegret A j q mu0 (mu0+eps) := le_max_left _ _
  have hg : frozenValue (p q (mass q mu0)) (D6FrozenScalarAllocation.beta q (mass q mu0)) (mu0+eps) ≤
      D6PhaseThreeSharp.rate q (mu0+eps) := by linarith only [hd,hr]
  have hleft : 0 ≤ leftCoefficient q := by unfold leftCoefficient D6ExpandedAllocation.value; positivity
  have h := separation_lower (p q (mass q mu0)) (D6FrozenScalarAllocation.beta q (mass q mu0)) (leftCoefficient q)
    mu0 eps (D6PhaseThreeSharp.rate q (mu0+eps)) hc.2.1.le hc.2.2.1 hleft hb hg
  simpa only [left_rate,localJump] using h

open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6GaussianQueryDominance
open CIGAMF.P13.D6AdaptiveTranscript CIGAMF.P13.D6AdaptiveOracleRegret
variable {H : Type*} [MeasurableSpace H]

/-- The matching leading lower bound on the real adaptive transcript law.
The nuisance feasibility conditions are the same explicit local-neighborhood
conditions used in the co-moving adversary theorem. -/
theorem adaptive_lower_leading (A : Finset (I n)) (j : I n) (q mu0 eps : ℝ)
    (hq : 3 ≤ q) (hI : Interior q (1-mu0)) (hmI : Interior q (1-(mu0-eps)))
    (h0lo : marginMax q ≤ mu0) (hplushi : mu0+eps ≤ marginHigh q) (heps : 0 ≤ eps)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (hnulo : eps ≤ 1-(1-mu0)*(1+D6ExpandedAllocation.root q (D6ExpandedAllocation.scale q)))
    (hnuhi : eps ≤ (1-mu0)*(1+D6ExpandedAllocation.root q (D6ExpandedAllocation.scale q)))
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (policy : ℕ → H → Measurement n) (legal : ∀ t h,Legal j q (policy t h))
    (ha : ∀ t,Measurable (fun h => meanOffset A j (policy t h)))
    (hb : ∀ t,Measurable (fun h => meanSlope A j (policy t h)))
    (update : ℕ → H × ℝ → H) (hu : ∀ t,Measurable (update t))
    (E : Finset (Measurement n)) (w : H → Measurement n → ℝ)
    (feasible : ∀ h,Feasible j q E (w h))
    (hmLoss : Measurable (fun h => oracleRegret A j q (mu0-eps) E (w h)))
    (hpLoss : Measurable (fun h => oracleRegret A j q (mu0+eps) E (w h)))
    (N : ℕ) (hN : 0 < N) :
    ∃ hm : ∀ mu t,Measurable (fun h => actualMean A j mu (policy t h)),
      localJump q mu0*eps*standardTail (q*eps*Real.sqrt N)-eps^2 ≤
      max
        (∫ h,oracleRegret A j q (mu0-eps) E (w h) ∂trajectory initial
          (fun t => actualStep (fun h => actualMean A j (mu0-eps) (policy t h))
            (hm (mu0-eps) t) (update t) (hu t)) N ())
        (∫ h,oracleRegret A j q (mu0+eps) E (w h) ∂trajectory initial
          (fun t => actualStep (fun h => actualMean A j (mu0+eps) (policy t h))
            (hm (mu0+eps) t) (update t) (hu t)) N ()) := by
  have hpLo : marginMax q ≤ mu0+eps := by linarith
  have hrate : (1-mu0)+eps=1-(mu0-eps) := by ring
  have hminus : Interior q ((1-mu0)+eps) := by rwa [hrate]
  obtain ⟨hm,hlower⟩ := adaptive_oracle_regret_lower A j q (1-mu0) eps hq hI hminus
    (by simpa only [sub_sub_cancel] using hpLo)
    (by simpa only [sub_sub_cancel] using hplushi) hj hA hB heps hnulo hnuhi
    initial policy legal ha hb update hu E w feasible
    (by simpa only [sub_sub_cancel] using hmLoss)
    (by simpa only [sub_sub_cancel] using hpLoss) N hN
  simp only [sub_sub_cancel] at hlower
  rw [hrate] at hlower
  refine ⟨hm,?_⟩
  apply le_trans ?_ hlower
  have hs := adaptive_separation_leading A j q mu0 eps hq hI h0lo hplushi heps hj hA hB
  have ht : 0 ≤ standardTail (q*eps*Real.sqrt N) := ENNReal.toReal_nonneg
  have ht1 : standardTail (q*eps*Real.sqrt N) ≤ 1 := measureReal_le_one
  have hst := mul_le_mul_of_nonneg_right hs ht
  have hcor := mul_le_mul_of_nonneg_left ht1 (sq_nonneg eps)
  nlinarith only [hst,hcor]

#print axioms constructive_upper
#print axioms adaptive_separation_leading
#print axioms adaptive_lower_leading
end
end CIGAMF.P13.D6KnownLabelMatchingRisk
