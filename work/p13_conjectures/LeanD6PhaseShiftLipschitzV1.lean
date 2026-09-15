import «LeanD6AllocationPhaseThreeParametersV1»

/-! An explicit finite-neighborhood modulus for the radical nuisance shift.
This controls the frozen-design oracle remainder without an asymptotic axiom. -/
namespace CIGAMF.P13.D6PhaseShiftLipschitz
open CIGAMF.P13.D6AllocationPhaseThreeParameters
noncomputable section

lemma unit_square_bound (x y eps : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : 0 ≤ y) (hy1 : y ≤ 1) (heps : 0 ≤ eps) (he : |x-y| ≤ eps) :
    |x^2-y^2| ≤ 2*eps := by
  have hi : x^2-y^2=(x-y)*(x+y) := by ring
  rw [hi,abs_mul,abs_of_nonneg (add_nonneg hx hy)]
  have h := mul_le_mul he (show x+y ≤ 2 by linarith) (add_nonneg hx hy) heps
  nlinarith only [h]

lemma radicand_difference_bound (q x y eps : ℝ) (hq : 3 ≤ q)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (heps : 0 ≤ eps) (he : |x-y| ≤ eps) :
    |radicand q x-radicand q y| ≤ 2*(q*(q-1)+K q)*eps := by
  have ha : 0 ≤ q*(q-1) := mul_nonneg (by linarith) (by linarith)
  have hk := (K_pos q hq).le
  have hsq := unit_square_bound x y eps hx hx1 hy hy1 heps he
  have hcomp : |(1-x)-(1-y)| ≤ eps := by
    have heq : (1-x)-(1-y)= -(x-y) := by ring
    rwa [heq,abs_neg]
  have hsqc := unit_square_bound (1-x) (1-y) eps (by linarith) (by linarith)
    (by linarith) (by linarith) heps hcomp
  have hid : radicand q x-radicand q y=
      q*(q-1)*((1-x)^2-(1-y)^2)+K q*(x^2-y^2) := by unfold radicand; ring
  rw [hid]
  calc
    _ ≤ |q*(q-1)*((1-x)^2-(1-y)^2)|+|K q*(x^2-y^2)| := abs_add_le _ _
    _ = q*(q-1)* |(1-x)^2-(1-y)^2|+K q* |x^2-y^2| := by
      rw [abs_mul (q*(q-1)),abs_mul (K q),abs_of_nonneg ha,abs_of_nonneg hk]
    _ ≤ q*(q-1)*(2*eps)+K q*(2*eps) :=
      add_le_add (mul_le_mul_of_nonneg_left hsqc ha) (mul_le_mul_of_nonneg_left hsq hk)
    _ = _ := by ring

def radicalModulus (q mu0 : ℝ) := 2*(q*(q-1)+K q)/D q mu0
def shiftModulus (q mu0 : ℝ) := (q*(q-2)+radicalModulus q mu0)/K q

theorem radical_lipschitz (q mu mu0 eps : ℝ) (hq : 3 ≤ q)
    (hm : 0 < mu) (hm1 : mu ≤ 1) (hm0 : 0 < mu0) (hm01 : mu0 ≤ 1)
    (heps : 0 ≤ eps) (he : |mu-mu0| ≤ eps) :
    |D q mu-D q mu0| ≤ radicalModulus q mu0*eps := by
  have hd := radical_positive q mu hq hm
  have hd0 := radical_positive q mu0 hq hm0
  have hrad := radicand_difference_bound q mu mu0 eps hq hm.le hm1 hm0.le hm01 heps he
  have hi : (D q mu-D q mu0)*(D q mu+D q mu0)=radicand q mu-radicand q mu0 := by
    nlinarith only [radical_square q mu hq,radical_square q mu0 hq]
  have ha := congrArg abs hi
  rw [abs_mul,abs_of_pos (add_pos hd hd0)] at ha
  have hle : |D q mu-D q mu0| *D q mu0 ≤ 2*(q*(q-1)+K q)*eps := by
    have h := mul_nonneg (abs_nonneg (D q mu-D q mu0)) hd.le
    nlinarith only [ha,hrad,h]
  calc
    |D q mu-D q mu0| ≤ (2*(q*(q-1)+K q)*eps)/D q mu0 := (le_div_iff₀ hd0).mpr hle
    _ = radicalModulus q mu0*eps := by unfold radicalModulus; ring

theorem shift_lipschitz (q mu mu0 eps : ℝ) (hq : 3 ≤ q)
    (hm : 0 < mu) (hm1 : mu ≤ 1) (hm0 : 0 < mu0) (hm01 : mu0 ≤ 1)
    (heps : 0 ≤ eps) (he : |mu-mu0| ≤ eps) :
    |shift q mu-shift q mu0| ≤ shiftModulus q mu0*eps := by
  have hk := K_pos q hq
  have hq2 : 0 ≤ q*(q-2) := mul_nonneg (by linarith) (by linarith)
  have hrad := radical_lipschitz q mu mu0 eps hq hm hm1 hm0 hm01 heps he
  have hi : K q*(shift q mu-shift q mu0)=
      -(q*(q-2)*(mu-mu0))-(D q mu-D q mu0) := by
    nlinarith only [rationalized_shift q mu hq hm hm1,rationalized_shift q mu0 hq hm0 hm01]
  have ha := congrArg abs hi
  rw [abs_mul,abs_of_pos hk] at ha
  have hb : K q* |shift q mu-shift q mu0| ≤ (q*(q-2)+radicalModulus q mu0)*eps := by
    rw [ha]
    calc
      _ ≤ |-(q*(q-2)*(mu-mu0))|+|D q mu-D q mu0| := abs_sub _ _
      _ = q*(q-2)* |mu-mu0|+|D q mu-D q mu0| := by rw [abs_neg,abs_mul,abs_of_nonneg hq2]
      _ ≤ q*(q-2)*eps+radicalModulus q mu0*eps :=
        add_le_add (mul_le_mul_of_nonneg_left he hq2) hrad
      _ = _ := by ring
  calc
    |shift q mu-shift q mu0| ≤ ((q*(q-2)+radicalModulus q mu0)*eps)/K q :=
      (le_div_iff₀ hk).mpr (by simpa only [mul_comm] using hb)
    _ = shiftModulus q mu0*eps := by unfold shiftModulus; ring

#print axioms radicand_difference_bound
#print axioms radical_lipschitz
#print axioms shift_lipschitz
end
end CIGAMF.P13.D6PhaseShiftLipschitz
