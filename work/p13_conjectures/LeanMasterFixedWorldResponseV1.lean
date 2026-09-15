import «LeanD6ReferenceFullCountLossV1»
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Change the reference of a fixed compensated world, not its compensation.
The chosen experiment observes a Gaussian response slope. Raw function samples
are a different experiment and no equality of their laws is asserted. -/
namespace CIGAMF.P13.MasterFixedWorldResponse
open Finset
open scoped BigOperators NNReal
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.P13.D6ReferenceFullCountLoss
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

def responseSlope (t : ℝ) (F : (I n → Bool) → ℝ) (i : I n) : ℝ :=
  productResponse (bern t) F i true-productResponse (bern t) F i false

lemma fixed_response_split (t t0 : ℝ) (A T : Finset (I n)) (j : I n) (rho : ℝ)
    (i : I n) (u : Bool) :
    productResponse (bern t) (centeredWorld A T j rho t0) i u =
      productResponse (bern t) (gate A j) i u+
      productResponse (bern t) (linear (compensation A T j rho t0)) i u-shift A T j rho t0 := by
  classical
  have hconst : (∑ c : I n → Bool,jointWeight (bern t) c*shift A T j rho t0)=shift A T j rho t0 := by
    rw [← sum_mul,bern_normalized,one_mul]
  unfold productResponse productExpectation centeredWorld
  simp_rw [mul_sub,mul_add]
  rw [sum_sub_distrib,sum_add_distrib,hconst]

/-- Compensation and centering remain fixed at t0 in the actual function. -/
theorem fixed_world_slope (t t0 : ℝ) (A T : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (hB : 2 ≤ (others A j).card) (rho : ℝ) (i : I n) :
    responseSlope t (centeredWorld A T j rho t0) i=
      target T rho i+gateSlope t A j i-gateSlope t0 A j i := by
  unfold responseSlope
  rw [fixed_response_split,fixed_response_split,
    gate_response_levels t A j hjA hB i true,gate_response_levels t A j hjA hB i false,
    response_linear t (compensation A T j rho t0) i true,
    response_linear t (compensation A T j rho t0) i false]
  simp only [bit_true,bit_false,compensation]
  ring

/-- Swap hidden membership of i between equal-size worlds. The mean contrast
is the change in the gate's a-b gap, with the original reference held fixed. -/
theorem fixed_world_contrast (t t0 : ℝ) (A B T : Finset (I n)) (j i : I n)
    (hjA : j ∉ A) (hjB : j ∉ B) (hBA : 2 ≤ (others A j).card)
    (hBB : 2 ≤ (others B j).card) (hcard : A.card=B.card)
    (hother : (others A j).card=(others B j).card)
    (hiA : i ∈ A) (hiB : i ∉ B) (rho : ℝ) :
    responseSlope t (centeredWorld A T j rho t0) i-
      responseSlope t (centeredWorld B T j rho t0) i=
      (1-t)^(A.card+(others A j).card-1)-(1-t0)^(A.card+(others A j).card-1) := by
  have hij : i ≠ j := by intro he;subst i;exact hjA hiA
  rw [fixed_world_slope t t0 A T j hjA hBA rho i,fixed_world_slope t t0 B T j hjB hBB rho i,
    gateSlope_mem_A t A j i hij hiA,gateSlope_mem_A t0 A j i hij hiA,
    gateSlope_others t B j i hij hiB,gateSlope_others t0 B j i hij hiB]
  have hb (u : ℝ) : slopeBval u B j=slopeBval u A j := by unfold slopeBval;rw [hcard,hother]
  rw [hb,hb]
  have h := slope_gap t A j hBA
  have h0 := slope_gap t0 A j hBA
  linarith

/-- Explicit observation model: a Gaussian instrument measuring the slope. -/
def instrumentLaw (t : ℝ) (F : (I n → Bool) → ℝ) (i : I n) (variance : ℝ≥0) :=
  ProbabilityTheory.gaussianReal (responseSlope t F i) variance

/-- Same law at the installed reference for this specified instrument. -/
theorem instrument_at_reference (t0 : ℝ) (A T : Finset (I n)) (j i : I n)
    (hjA : j ∉ A) (hB : 2 ≤ (others A j).card) (rho : ℝ) (variance : ℝ≥0) :
    instrumentLaw t0 (centeredWorld A T j rho t0) i variance=
      ProbabilityTheory.gaussianReal (target T rho i) variance := by
  unfold instrumentLaw
  rw [fixed_world_slope t0 t0 A T j hjA hB rho i]
  congr 1
  ring

/-- Local reference sensitivity, separate from any sample-cost theorem. -/
theorem contrast_derivative (k : ℕ) (t0 t : ℝ) :
    HasDerivAt (fun u : ℝ => (1-u)^k-(1-t0)^k) (-(k:ℝ)*(1-t)^(k-1)) t := by
  have hbase : HasDerivAt (fun u : ℝ => 1-u) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  convert (hbase.pow k).sub_const ((1-t0)^k) using 1 <;> (try rfl) <;> ring

#print axioms fixed_world_slope
#print axioms fixed_world_contrast
#print axioms instrument_at_reference
#print axioms contrast_derivative
end
end CIGAMF.P13.MasterFixedWorldResponse
