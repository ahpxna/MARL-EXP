import «LeanD6ScaledReferenceCoefficientsV1»

/-! Explicit finite-size coefficient error; no asymptotic O-notation premises. -/
namespace CIGAMF.P13.D6ScaledReferenceError
open CIGAMF.P13.D6ScaledReferenceCoefficients
noncomputable section

lemma exp_difference (x y : ℝ) (hxy : x ≤ y) (hy : y ≤ 0) :
    Real.exp y-Real.exp x ≤ y-x := by
  have he : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr hy
  have hg := Real.add_one_le_exp (x-y)
  have hd : 0 ≤ 1-Real.exp (x-y) := by
    have := Real.exp_le_one_iff.mpr (show x-y ≤ 0 by linarith)
    linarith
  have hid : Real.exp x=Real.exp y*Real.exp (x-y) := by rw [← Real.exp_add];congr 1;ring
  rw [hid]
  nlinarith [mul_nonneg (show 0 ≤ 1-Real.exp y by linarith) hd]

lemma exp_nonpos_lipschitz (x y : ℝ) (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x-Real.exp y| ≤ |x-y| := by
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h)),abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [exp_difference x y h hy]
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),abs_of_nonneg (sub_nonneg.mpr h)]
    exact exp_difference y x h hx

/-- Uniform O(1/k) logarithmic bound at t=tau/k, valid for k>=2tau. -/
theorem log_coefficient_error (tau : ℝ) (ht : 0 ≤ tau) (k : ℕ)
    (hk : 1 ≤ k) (hkt : 2*tau ≤ (k:ℝ)) :
    |Real.log (c tau k)+2*tau| ≤ (2*tau+4*tau^2)/(k:ℝ) := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hx : 0 ≤ tau/(k:ℝ) := div_nonneg ht hkpos.le
  have hx1 : tau/(k:ℝ) ≤ 1/2 := (div_le_iff₀ hkpos).mpr (by linarith)
  have hp : 0 < 1-tau/(k:ℝ) := by linarith
  have hr := log_one_sub_bound (tau/(k:ℝ)) hx hx1
  have hm : ((2*k-2:ℕ):ℝ)=2*(k:ℝ)-2 := by
    rw [Nat.cast_sub (by omega),Nat.cast_mul]
    norm_num
  have hid : Real.log (c tau k)+2*tau=
      (2*(k:ℝ)-2)*(Real.log (1-tau/(k:ℝ))+tau/(k:ℝ))+2*tau/(k:ℝ) := by
    unfold c
    rw [Real.log_pow,hm]
    field_simp
    <;> ring
  rw [hid]
  have hn : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hbound := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*(k:ℝ)-2 by linarith)
  have htri := abs_add_le ((2*(k:ℝ)-2)*(Real.log (1-tau/(k:ℝ))+tau/(k:ℝ))) (2*tau/(k:ℝ))
  rw [abs_mul,abs_of_nonneg (show 0 ≤ 2*(k:ℝ)-2 by linarith),abs_of_nonneg (show 0 ≤ 2*tau/(k:ℝ) by positivity)] at htri
  have heq : (2*(k:ℝ)-2)*(2*(tau/(k:ℝ))^2)+2*tau/(k:ℝ)=
      (2*tau+4*tau^2)/(k:ℝ)-4*tau^2/(k:ℝ)^2 := by field_simp;ring
  have hnon : 0 ≤ 4*tau^2/(k:ℝ)^2 := by positivity
  linarith

/-- An explicit constant, uniform in tau on every bounded positive interval. -/
theorem coefficient_error (tau : ℝ) (ht : 0 ≤ tau) (k : ℕ)
    (hk : 1 ≤ k) (hkt : 2*tau ≤ (k:ℝ)) :
    |c tau k-limitC tau| ≤ (2*tau+4*tau^2)/(k:ℝ) := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hx : 0 ≤ tau/(k:ℝ) := div_nonneg ht hkpos.le
  have hx1 : tau/(k:ℝ) ≤ 1/2 := (div_le_iff₀ hkpos).mpr (by linarith)
  have hp : 0 < c tau k := pow_pos (by linarith) _
  have hcle : c tau k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hl : Real.log (c tau k) ≤ 0 := Real.log_nonpos hp.le hcle
  have he := exp_nonpos_lipschitz (Real.log (c tau k)) (-2*tau) hl (by linarith)
  rw [Real.exp_log hp] at he
  exact he.trans (by simpa [sub_neg_eq_add] using log_coefficient_error tau ht k hk hkt)

#print axioms exp_nonpos_lipschitz
#print axioms log_coefficient_error
#print axioms coefficient_error
end
end CIGAMF.P13.D6ScaledReferenceError
