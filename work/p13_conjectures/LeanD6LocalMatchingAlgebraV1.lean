import «LeanD6FrozenOracleGapV1»

/-! Finite-epsilon risk algebra. All constants are explicit; no asymptotic
notation or statistical assumption substitutes for the actual risk bridge. -/
namespace CIGAMF.P13.D6LocalMatchingAlgebra
noncomputable section

def leftValue (c mu : ℝ) := c*(1-mu)^2/2
def frozenValue (p b mu : ℝ) := (p*mu^2+b*(1-mu)^2)/2
def jump (p b c mu0 : ℝ) := p*mu0-b*(1-mu0)+c*(1-mu0)
def curvatureDifference (p b c : ℝ) := (p+b-c)/2

theorem exact_difference (p b c mu0 eps : ℝ)
    (h0 : frozenValue p b mu0=leftValue c mu0) :
    frozenValue p b (mu0+eps)-leftValue c (mu0+eps)=
      jump p b c mu0*eps+curvatureDifference p b c*eps^2 := by
  unfold frozenValue leftValue at h0
  unfold frozenValue leftValue jump curvatureDifference
  nlinarith only [h0]

theorem jump_positive (p b c mu0 : ℝ) (hp : 0 < p) (hm0 : 0 < mu0) (hm1 : mu0 < 1)
    (h0 : frozenValue p b mu0=leftValue c mu0) : 0 < jump p b c mu0 := by
  have h := D6FrozenOracleGap.boundary_slope_jump p b c mu0 (ne_of_lt hm1) h0
  unfold jump
  rw [h]
  exact div_pos (mul_pos hp hm0) (by linarith)

/-- Exact two-margin separation is at least J epsilon - epsilon^2. -/
theorem separation_lower (p b c mu0 eps gammaPlus : ℝ)
    (hp : 0 ≤ p) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h0 : frozenValue p b mu0=leftValue c mu0)
    (hg : frozenValue p b (mu0+eps) ≤ gammaPlus) :
    jump p b c mu0*eps-eps^2 ≤
      leftValue c (mu0-eps)+gammaPlus-2*leftValue c mu0-eps^2 := by
  have hsq : 0 ≤ (p+b+c)*eps^2 := mul_nonneg (by linarith) (sq_nonneg _)
  unfold frozenValue leftValue at h0
  unfold frozenValue at hg
  unfold jump leftValue
  nlinarith only [h0,hg,hsq]

/-- Both losses of the threshold rule obey the same leading constant. -/
theorem threshold_pair_upper (p b c mu0 eps t Rminus Rplus wrongPlus M : ℝ)
    (h0 : frozenValue p b mu0=leftValue c mu0)
    (he : 0 ≤ eps) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hJ : 0 ≤ jump p b c mu0) (hM : 0 ≤ M)
    (hm : Rminus=max 0 (leftValue c (mu0-eps)-frozenValue p b (mu0-eps)))
    (hp0 : 0 ≤ Rplus) (hp : Rplus ≤ M*eps^2)
    (hwrong : wrongPlus ≤ max 0 (frozenValue p b (mu0+eps)+Rplus-leftValue c (mu0+eps))) :
    max (Rminus*t) (Rplus+(wrongPlus-Rplus)*t) ≤
      jump p b c mu0*eps*t+(M+|curvatureDifference p b c|)*eps^2 := by
  have hd := exact_difference p b c mu0 eps h0
  have hdm := exact_difference p b c mu0 (-eps) h0
  simp only [← sub_eq_add_neg] at hdm
  have hcur := le_abs_self (curvatureDifference p b c)
  have hcur' := neg_le_abs (curvatureDifference p b c)
  have hcur0 := abs_nonneg (curvatureDifference p b c)
  have hbase : 0 ≤ jump p b c mu0*eps+|curvatureDifference p b c| *eps^2 := by positivity
  have hneg : leftValue c (mu0-eps)-frozenValue p b (mu0-eps) ≤
      jump p b c mu0*eps+|curvatureDifference p b c| *eps^2 := by
    have h := mul_le_mul_of_nonneg_right hcur' (sq_nonneg eps)
    nlinarith only [hdm,h]
  have hm' : Rminus ≤ jump p b c mu0*eps+|curvatureDifference p b c| *eps^2 := by
    rw [hm]
    exact max_le hbase hneg
  have hp' : wrongPlus ≤ Rplus+jump p b c mu0*eps+|curvatureDifference p b c| *eps^2 := by
    apply hwrong.trans
    apply max_le
    · linarith only [hbase,hp0]
    · have h := mul_le_mul_of_nonneg_right hcur (sq_nonneg eps)
      linarith only [hd,h]
  have hmt := mul_le_mul_of_nonneg_right hm' ht
  have hpt := mul_le_mul_of_nonneg_right hp' ht
  have hct := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hcur0 (sq_nonneg eps))
  have hMe : 0 ≤ M*eps^2 := mul_nonneg hM (sq_nonneg eps)
  apply max_le <;> nlinarith only [hmt,hpt,hct,hp,hMe]

#print axioms exact_difference
#print axioms jump_positive
#print axioms separation_lower
#print axioms threshold_pair_upper
end
end CIGAMF.P13.D6LocalMatchingAlgebra
