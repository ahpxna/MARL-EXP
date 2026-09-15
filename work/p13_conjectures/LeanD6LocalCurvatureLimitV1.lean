import «LeanD6GrowingPhaseThreeRemainderV1»
import «LeanD6LocalMatchingDesignV1»

/-! # The local curvature does not vanish with q

`LeanD6GrowingPhaseThreeRemainderV1.remainder_scaled` bounds the frozen
remainder constant by `64/q^2`.  The matching-risk bounds of
`LeanD6KnownLabelMatchingRiskV1` and `LeanD6ActualSampleMatchingV1` carry the
coefficient `remainderConstant q mu0 + |localCurvature q mu0|`, so it is
natural to look for a matching `O(1/q^2)` bound on the second summand.

There is none, and this module proves it.  On the phase-III interval

  `-(1/2) < localCurvature q mu <= -(1/2) + 2/q`   for every `q >= 8`,

the sandwich implies `|localCurvature q mu| -> 1/2` along admissible margins.
The matching coefficient is `Theta(1)`, squeezed into
`[1/2 - 2/q, 1/2 + 64/q^2]`. This does not obstruct growing-q matching:
the coefficient multiplies epsilon^2, which is O(q^-3) on the critical
epsilon=O(q^-3/2) scale, below the q^-2 target. The formal statements here
are the finite inequalities; asymptotic language describes their consequences.

The mechanism is a property of the design, not of the proof technique.  Both
frozen parameters vanish -- `p q w = (1-w)/q <= 1/q`, and `beta q w <= w` with
`w = mass q mu <= 1/(q-2)^2` -- while the left allocation's coefficient
`value q (scale q)` tends to one from below, because `scale q = sqrt(q/(q+1))`
tends to one.  The curvature difference `(p + beta - c)/2` inherits the gap.
-/
namespace CIGAMF.P13.D6LocalCurvatureLimit
open CIGAMF.P13.D6AllocationPhaseThreeCore CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationPhaseThreeFeasible CIGAMF.P13.D6AllocationMarginRegion
open CIGAMF.P13.D6FrozenScalarAllocation CIGAMF.P13.D6FrozenQuadraticBound
open CIGAMF.P13.D6LocalMatchingAlgebra CIGAMF.P13.D6LocalMatchingDesign
open CIGAMF.P13.D6UniformPhaseThreeRemainder CIGAMF.P13.D6GrowingPhaseThreeRemainder
noncomputable section
variable {q mu : ℝ}

/-! ## The left allocation's coefficient tends to one -/

lemma scale_pos (hq : (3:ℝ) ≤ q) : 0 < D6ExpandedAllocation.scale q := by
  unfold D6ExpandedAllocation.scale
  exact Real.sqrt_pos.mpr (div_pos (by linarith) (by linarith))

lemma scale_lt_one (hq : (3:ℝ) ≤ q) : D6ExpandedAllocation.scale q < 1 := by
  unfold D6ExpandedAllocation.scale
  have hlt : q/(q+1) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have h := Real.sqrt_lt_sqrt (div_nonneg (by linarith) (by linarith)) hlt
  rwa [Real.sqrt_one] at h

/-- `sqrt(q/(q+1)) >= (q-1)/q`.  Squaring is legitimate because both sides are
nonnegative; the resulting polynomial inequality is `q^2+q >= 1`. -/
lemma scale_ge (hq : (8:ℝ) ≤ q) : (q-1)/q ≤ D6ExpandedAllocation.scale q := by
  have hq0 : (0:ℝ) < q := by linarith
  have hb : (0:ℝ) ≤ (q-1)/q := div_nonneg (by linarith) hq0.le
  have hsq : ((q-1)/q)^2 ≤ q/(q+1) := by
    rw [div_pow, div_le_iff₀ (pow_pos hq0 2), div_mul_eq_mul_div,
      le_div_iff₀ (by linarith : (0:ℝ) < q+1)]
    nlinarith
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hb] at h

lemma left_lt_one (hq : (8:ℝ) ≤ q) : leftCoefficient q < 1 := by
  have hq3 : (3:ℝ) ≤ q := by linarith
  have hc0 := scale_pos hq3
  have hc1 := scale_lt_one hq3
  have hden : 0 < q - 2 + D6ExpandedAllocation.scale q := by linarith
  have hr : D6ExpandedAllocation.scale q*(q-1)/(q-2+D6ExpandedAllocation.scale q) < 1 := by
    rw [div_lt_one hden]; nlinarith
  have hr0 : 0 ≤ D6ExpandedAllocation.scale q*(q-1)/(q-2+D6ExpandedAllocation.scale q) :=
    div_nonneg (by nlinarith) hden.le
  unfold leftCoefficient D6ExpandedAllocation.value
  nlinarith

lemma left_ge (hq : (8:ℝ) ≤ q) : ((q-1)/q)^2 ≤ leftCoefficient q := by
  have hq0 : (0:ℝ) < q := by linarith
  have hq3 : (3:ℝ) ≤ q := by linarith
  have hc0 := scale_pos hq3
  have hc1 := scale_lt_one hq3
  have hcg := scale_ge hq
  have hden : 0 < q - 2 + D6ExpandedAllocation.scale q := by linarith
  have hqne : q ≠ 0 := ne_of_gt hq0
  have he : (q-1)/q*q = q-1 := by field_simp
  have hcq : q - 1 ≤ D6ExpandedAllocation.scale q*q := by
    have h := mul_le_mul_of_nonneg_right hcg hq0.le
    rwa [he] at h
  have hratio : (q-1)/q ≤
      D6ExpandedAllocation.scale q*(q-1)/(q-2+D6ExpandedAllocation.scale q) := by
    rw [le_div_iff₀ hden, div_mul_eq_mul_div, div_le_iff₀ hq0]
    nlinarith [mul_le_mul_of_nonneg_right hcq (by linarith : (0:ℝ) ≤ q-1),
      mul_lt_mul_of_pos_right hc1 (by linarith : (0:ℝ) < q-1)]
  have hb : (0:ℝ) ≤ (q-1)/q := div_nonneg (by linarith) hq0.le
  unfold leftCoefficient D6ExpandedAllocation.value
  nlinarith [hratio, hb]

/-! ## Both frozen parameters vanish -/

lemma coefficient_nonneg (hq : (3:ℝ) ≤ q) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1/4) :
    0 ≤ coefficient q w := by
  unfold coefficient
  have h1 : 0 ≤ (1-w)*(q-1)/q := div_nonneg (by nlinarith) (by linarith)
  have h2 : 0 ≤ w*(q-2)^2 := mul_nonneg hw0 (sq_nonneg _)
  linarith

/-- `beta q w <= w`: the extra `w*(q-2)^2` in the denominator only helps. -/
lemma beta_le (hq : (3:ℝ) ≤ q) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1/4) :
    beta q w ≤ w := by
  have hq0 : (0:ℝ) < q := by linarith
  have hd1 : 0 < (1-w)*(q-1) := by nlinarith
  have hd2 : (1-w)*(q-1) ≤ q*coefficient q w := by
    unfold coefficient
    have hqne : q ≠ 0 := ne_of_gt hq0
    have hx : q*((1-w)*(q-1)/q+w*(q-2)^2) = (1-w)*(q-1)+q*(w*(q-2)^2) := by
      field_simp <;> ring
    have h3 : 0 ≤ q*(w*(q-2)^2) :=
      mul_nonneg (by linarith) (mul_nonneg hw0 (sq_nonneg _))
    rw [hx]; linarith
  have hdpos : 0 < q*coefficient q w := by linarith
  unfold beta
  rw [div_le_iff₀ hdpos]
  nlinarith [mul_le_mul_of_nonneg_left hd2 hw0]

lemma mass_le (hq : (8:ℝ) ≤ q) (hm : mu ∈ phaseInterval q) :
    mass q mu ≤ 1/(q-2)^2 := by
  have hp : (0:ℝ) < (q-2)^2 := pow_pos (by linarith) 2
  rw [le_div_iff₀ hp]
  linarith [mass_scaled q mu hq hm]

/-! ## The sandwich -/

/-- The local curvature is trapped in `(-(1/2), -(1/2)+2/q]` for every `q>=8`
and every margin in the closed phase-III interval.  The lower bound uses only
`leftCoefficient q < 1`; the upper bound uses `leftCoefficient q >= ((q-1)/q)^2`
together with `p <= 1/q` and `beta <= 1/(q-2)^2 <= 1/q`. -/
theorem local_curvature_sandwich (hq : (8:ℝ) ≤ q) (hm : mu ∈ phaseInterval q) :
    -(1/2) < localCurvature q mu ∧ localCurvature q mu ≤ -(1/2)+2/q := by
  have hq0 : (0:ℝ) < q := by linarith
  have hq3 : (3:ℝ) ≤ q := by linarith
  obtain ⟨hw0,hw1⟩ := phase_mass_bounds q mu hq3 hm.1 hm.2
  have hmle := mass_le hq hm
  have hbeta := beta_le hq3 hw0 hw1
  have hbeta0 : 0 ≤ beta q (mass q mu) := by
    unfold beta
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hw0
    · exact mul_nonneg (by linarith) (coefficient_nonneg hq3 hw0 hw1)
  have hp0 : 0 ≤ p q (mass q mu) := by
    unfold p; exact div_nonneg (by linarith) hq0.le
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hone : (1:ℝ)/q*q = 1 := by field_simp
  have hple : p q (mass q mu) ≤ 1/q := by
    unfold p; rw [div_le_iff₀ hq0, hone]; linarith
  have hinv : 1/(q-2)^2 ≤ 1/q := by
    apply one_div_le_one_div_of_le hq0
    nlinarith
  have hb2 : beta q (mass q mu) ≤ 1/q := le_trans hbeta (le_trans hmle hinv)
  have hL1 := left_lt_one hq
  have hkey : ((q-1)/q)^2 = 1-2/q+1/q^2 := by field_simp <;> ring
  have hLge : 1-2/q+1/q^2 ≤ leftCoefficient q := by rw [← hkey]; exact left_ge hq
  have hq2 : (0:ℝ) ≤ 1/q^2 := by positivity
  unfold localCurvature curvatureDifference
  constructor
  · linarith
  · have htwo : (2:ℝ)/q=2*(1/q) := by ring
    rw [htwo] at hLge ⊢
    linarith

/-- Absolute form: the curvature magnitude rises to `1/2` and never reaches it. -/
theorem local_curvature_abs (hq : (8:ℝ) ≤ q) (hm : mu ∈ phaseInterval q) :
    1/2-2/q ≤ |localCurvature q mu| ∧ |localCurvature q mu| < 1/2 := by
  obtain ⟨hlo,hhi⟩ := local_curvature_sandwich hq hm
  have hq0 : (0:ℝ) < q := by linarith
  have h2q : 2/q ≤ 1/4 := by rw [div_le_iff₀ hq0]; linarith
  have hneg : localCurvature q mu ≤ 0 := by linarith
  rw [abs_of_nonpos hneg]
  constructor <;> linarith

/-- The matching-risk coefficient is `Theta(1)`, not `O(1/q^2)`.  The lower
bound tends to `1/2`, so no decaying bound on this coefficient exists, and the
`64/q^2` of `remainder_scaled` bounds only the smaller of the two summands. -/
theorem matching_coefficient_theta_one (hq : (8:ℝ) ≤ q) (hm : mu ∈ phaseInterval q) :
    1/2-2/q ≤ remainderConstant q mu+|localCurvature q mu| ∧
      remainderConstant q mu+|localCurvature q mu| ≤ 64/q^2+1/2 := by
  obtain ⟨hlo,hhi⟩ := local_curvature_abs hq hm
  have hq3 : (3:ℝ) ≤ q := by linarith
  obtain ⟨hw0,hw1⟩ := phase_mass_bounds q mu hq3 hm.1 hm.2
  have hr0 : 0 ≤ remainderConstant q mu := by
    unfold remainderConstant
    have hc := coefficient_nonneg hq3 hw0 hw1
    have hm2 : 0 ≤ coefficient q (mass q mu)*(combinedModulus q mu)^2 :=
      mul_nonneg hc (sq_nonneg _)
    linarith
  have hrs := remainder_scaled q mu hq hm
  constructor <;> linarith

#print axioms scale_ge
#print axioms left_lt_one
#print axioms left_ge
#print axioms beta_le
#print axioms mass_le
#print axioms local_curvature_sandwich
#print axioms local_curvature_abs
#print axioms matching_coefficient_theta_one
end
end CIGAMF.P13.D6LocalCurvatureLimit
