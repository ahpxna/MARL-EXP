import «LeanD6KnownLabelMatchingRiskV1»

/-! The constructive upper bound on raw observations from the legal B-off
query. The decision uses only q and the known boundary, not epsilon. -/
namespace CIGAMF.P13.D6ActualSampleMatching
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.AdaptiveTranscriptKernel CIGAMF.P13.GaussianSampleProduct
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6Threshold
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6LocalMatchingDesign
open CIGAMF.P13.D6KnownLabelMatchingRisk CIGAMF.P13.GaussianThresholdDecision
open CIGAMF.P13.D6AllocationMargin CIGAMF.P13.D6AllocationMarginRegion
open CIGAMF.P13.D6AllocationPhaseThreeFeasible CIGAMF.P13.D6FrozenQuadraticBound
open CIGAMF.P13.D6GaussianOverlap
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def statistic (q mu0 : ℝ) (N : ℕ) (x : Samples ℝ N) : ℝ :=
  (N:ℝ)*(1+q-q*mu0)-sumSamples N x

def rawRisk (A : Finset (I n)) (j : I n) (q mu0 mu : ℝ) (N : ℕ) : ℝ :=
  ∫ x,if 0 ≤ statistic q mu0 N x then rightRegret A j q mu0 mu
    else leftRegret A j q mu
    ∂resource (gaussianReal (actualMean A j mu (.inr (others A j,false))) 1) N ()

theorem actual_statistic_law (A : Finset (I n)) (j : I n) (q mu0 mu : ℝ)
    (hq : 2 ≤ q) (hj : j ∉ A) (hB : ((others A j).card : ℝ)=q) (N : ℕ) :
    HasLaw (statistic q mu0 N) (gaussianReal ((N:ℝ)*(q*(mu-mu0))) (N:NNReal))
      (resource (gaussianReal (actualMean A j mu (.inr (others A j,false))) 1) N ()) := by
  rw [B_off_mean A j q hq hj hB mu]
  have h := gaussianReal_const_sub (gaussian_sum_law (1+q-q*mu) N)
    ((N:ℝ)*(1+q-q*mu0))
  have he : (N:ℝ)*(1+q-q*mu0)-(N:ℝ)*(1+q-q*mu)=(N:ℝ)*(q*(mu-mu0)) := by ring
  rw [he] at h
  exact h

theorem raw_risk_identity (A : Finset (I n)) (j : I n) (q mu0 mu : ℝ)
    (hq : 2 ≤ q) (hj : j ∉ A) (hB : ((others A j).card : ℝ)=q) (N : ℕ) :
    rawRisk A j q mu0 mu N =
      ∫ x,if choosePlus N x then rightRegret A j q mu0 mu else leftRegret A j q mu
        ∂resource (gaussianReal (q*(mu-mu0)) 1) N () := by
  let f : ℝ → ℝ := fun x => if 0 ≤ x then rightRegret A j q mu0 mu else leftRegret A j q mu
  have hf : Measurable f := by
    exact Measurable.ite measurableSet_Ici measurable_const measurable_const
  have hraw := (actual_statistic_law A j q mu0 mu hq hj hB N).integral_comp hf.aestronglyMeasurable
  have hcenter := (gaussian_sum_law (q*(mu-mu0)) N).integral_comp hf.aestronglyMeasurable
  exact hraw.trans hcenter.symm

/-- Matching upper bound for a realizable experiment on the actual query
library. Both losses are the actual infimum-over-world oracle regrets. -/
theorem actual_constructive_upper (A : Finset (I n)) (j : I n) (q mu0 eps : ℝ)
    (hq : 3 ≤ q) (hI : Interior q (1-mu0)) (hmI : Interior q (1-(mu0-eps)))
    (h0lo : marginMax q ≤ mu0) (hplushi : mu0+eps ≤ marginHigh q)
    (hminus : 1/2 ≤ mu0-eps) (heps : 0 ≤ eps)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (N : ℕ) (hN : 0 < N) :
    max (rawRisk A j q mu0 (mu0-eps) N) (rawRisk A j q mu0 (mu0+eps) N) ≤
      localJump q mu0*eps*standardTail (q*eps*Real.sqrt N)+
        (remainderConstant q mu0+|localCurvature q mu0|)*eps^2 := by
  have hm : q*(mu0-eps-mu0)=-(q*eps) := by ring
  have hp : q*(mu0+eps-mu0)=q*eps := by ring
  rw [raw_risk_identity A j q mu0 (mu0-eps) (by linarith) hj hB N,
    raw_risk_identity A j q mu0 (mu0+eps) (by linarith) hj hB N,hm,hp]
  exact constructive_upper A j q mu0 eps hq hI hmI h0lo hplushi hminus heps hj hA hB N hN

#print axioms actual_statistic_law
#print axioms raw_risk_identity
#print axioms actual_constructive_upper
end
end CIGAMF.P13.D6ActualSampleMatching
