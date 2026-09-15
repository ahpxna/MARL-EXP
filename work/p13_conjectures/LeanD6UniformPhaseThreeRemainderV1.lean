import «LeanD6FrozenQuadraticBoundV1»

/-! A uniform finite quadratic-regret constant on the whole closed phase-III
interval, not an assumed bound on a random plug-in allocation. The compactness
proof is for fixed q; it deliberately supplies no sharp dependence on q. -/
namespace CIGAMF.P13.D6UniformPhaseThreeRemainder
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationPhaseThreeCore CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationPhaseThreeFeasible CIGAMF.P13.D6AllocationMarginRegion
open CIGAMF.P13.D6FrozenScalarAllocation CIGAMF.P13.D6FrozenAllocationFeasible
open CIGAMF.P13.D6PhaseShiftLipschitz CIGAMF.P13.D6FrozenQuadraticBound
open CIGAMF.P13.D6LocalOracleRegret CIGAMF.P13.D6PhaseThreePrimal
noncomputable section

def phaseInterval (q : ℝ) := Set.Icc (marginMax q) (marginHigh q)

lemma remainder_continuous (q : ℝ) (hq : 3 ≤ q) :
    ContinuousOn (remainderConstant q) (phaseInterval q) := by
  have hD : Continuous (D q) := by unfold D radicand; fun_prop
  have hDp : ∀ m ∈ phaseInterval q, 0 < D q m := by
    intro m hm
    have hb := phase_shift_bounds q m hq hm.1 hm.2
    exact radical_positive q m hq (by linarith [hb.1])
  have hden : ∀ m ∈ phaseInterval q, q*(q-2)*(1-m)+D q m ≠ 0 := by
    intro m hm
    have hb := phase_shift_bounds q m hq hm.1 hm.2
    have hn : 0 ≤ q*(q-2)*(1-m) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith [hb.2.1])
    linarith [hDp m hm]
  have hs : ContinuousOn (shift q) (phaseInterval q) := by
    unfold shift
    apply ContinuousOn.div (by fun_prop) (by fun_prop) hden
  have hm : ContinuousOn (mass q) (phaseInterval q) := by
    unfold mass
    exact (continuousOn_const.mul hs).div hD.continuousOn (fun m hm => ne_of_gt (hDp m hm))
  have hc : ContinuousOn (fun m => coefficient q (mass q m)) (phaseInterval q) := by
    unfold coefficient
    exact ((continuousOn_const.sub hm).mul continuousOn_const |>.div_const q).add
      (hm.mul continuousOn_const)
  have hcp : ∀ m ∈ phaseInterval q, coefficient q (mass q m) ≠ 0 := by
    intro m hx
    have hw := phase_mass_bounds q m hq hx.1 hx.2
    exact ne_of_gt (frozen_coefficients q (mass q m) hq hw.1 hw.2).1
  have hrad : ContinuousOn (radicalModulus q) (phaseInterval q) := by
    unfold radicalModulus
    exact continuousOn_const.div hD.continuousOn (fun m hx => ne_of_gt (hDp m hx))
  have hshift : ContinuousOn (shiftModulus q) (phaseInterval q) := by
    unfold shiftModulus
    exact (continuousOn_const.add hrad).div_const _
  have hcomb : ContinuousOn (combinedModulus q) (phaseInterval q) := by
    unfold combinedModulus
    exact hshift.add (((hm.mul continuousOn_const).div hc hcp).abs)
  unfold remainderConstant
  exact (hc.mul (hcomb.pow 2)).div_const 2

/-- A single nonnegative finite real C works simultaneously at all design
margins in phase III. It is derived from the actual explicit remainder. -/
theorem uniform_constant_exists (q : ℝ) (hq : 3 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ phaseInterval q, remainderConstant q z ≤ C := by
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (remainder_continuous q hq)
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro z hz
  exact (hB (Set.mem_image_of_mem (remainderConstant q) hz)).trans (le_max_right _ _)

/-- Uniform actual oracle regret over true/design margins in phase III.
There is no assumed modulus, oracle identity, or alternative feasibility. -/
theorem uniform_actual_quadratic (q : ℝ) (hq : 3 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ} (A : Finset (I n)) (j : I n)
      (mu mu0 : ℝ), mu ∈ phaseInterval q → mu0 ∈ phaseInterval q →
      j ∉ A → (A.card:ℝ)=q+1 → ((others A j).card:ℝ)=q →
      oracleRegret A j q mu (queries A j) (weights A j q (mass q mu0)) ≤ C*(mu0-mu)^2 := by
  obtain ⟨C,hC,hbound⟩ := uniform_constant_exists q hq
  refine ⟨C,hC,?_⟩
  intro n A j mu mu0 hm h0 hj hA hB
  have hh := actual_frozen_quadratic_regret A j q mu mu0 |mu-mu0| hq hm.1 hm.2 h0.1 h0.2
    hj hA hB (abs_nonneg _) le_rfl
  rw [sq_abs] at hh
  have ht := mul_le_mul_of_nonneg_right (hbound mu0 h0) (sq_nonneg (mu-mu0))
  have he : (mu-mu0)^2=(mu0-mu)^2 := by ring
  rw [← he]
  exact hh.trans ht

#print axioms remainder_continuous
#print axioms uniform_constant_exists
#print axioms uniform_actual_quadratic
end
end CIGAMF.P13.D6UniformPhaseThreeRemainder
