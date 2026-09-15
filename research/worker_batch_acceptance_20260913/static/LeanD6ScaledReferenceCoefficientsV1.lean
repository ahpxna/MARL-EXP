import Mathlib

/-! Exact scaled-reference coefficients. This module proves coefficient facts;
applying an actual minimax certificate additionally requires its physical domain. -/
namespace CIGAMF.P13.D6ScaledReferenceCoefficients
open Filter
open scoped Topology
noncomputable section

def c (tau : ℝ) (k : ℕ) := (1-tau/(k:ℝ))^(2*k-2)
def a (tau : ℝ) (k : ℕ) := (1+((k:ℝ)-2)*tau/(k:ℝ))*c tau k
def b (tau : ℝ) (k : ℕ) := (((k:ℝ)-2)*tau/(k:ℝ))*c tau k
def e (tau : ℝ) (k : ℕ) := min (a tau k) (2*b tau k)
def threshold (tau : ℝ) (k : ℕ) := 2*a tau k-e tau k/(k:ℝ)
def limitC (tau : ℝ) := Real.exp (-2*tau)
def limitThreshold (tau : ℝ) := 2*(1+tau)*limitC tau

/-- Elementary finite log remainder, including x=0. -/
theorem log_one_sub_bound (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1/2) :
    |Real.log (1-x)+x| ≤ 2*x^2 := by
  have hp : 0 < 1-x := by linarith
  have hu := Real.log_le_sub_one_of_pos hp
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hid : 1-(1-x)⁻¹ = -x/(1-x) := by field_simp;ring
  rw [hid,neg_div] at hl
  have hr : x/(1-x)-x ≤ 2*x^2 := by
    have heq : x/(1-x)-x=x^2/(1-x) := by field_simp;ring
    rw [heq]
    apply (div_le_iff₀ hp).mpr
    nlinarith [sq_nonneg x]
  rw [abs_of_nonpos (by linarith : Real.log (1-x)+x ≤ 0)]
  linarith

lemma base_tendsto (tau : ℝ) : Tendsto (fun k : ℕ => 1-tau/(k:ℝ)) atTop (𝓝 1) := by
  have hd : Tendsto (fun k : ℕ => tau/(k:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa using (show Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub hd

/-- The exponent 2k-2 is accounted for exactly, not replaced by 2k. -/
theorem c_tendsto (tau : ℝ) : Tendsto (c tau) atTop (𝓝 (limitC tau)) := by
  have hpow : Tendsto (fun k : ℕ => (1-tau/(k:ℝ))^k) atTop (𝓝 (Real.exp (-tau))) := by
    simpa [sub_eq_add_neg,neg_div] using Real.tendsto_one_add_div_pow_exp (-tau)
  have hlim := (hpow.pow 2).div ((base_tendsto tau).pow 2) (by norm_num)
  have heq : Real.exp (-tau)^2/(1:ℝ)^2=limitC tau := by
    simp only [one_pow,div_one,limitC,← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq] at hlim
  apply hlim.congr'
  have hb := (base_tendsto tau).eventually_ne (by norm_num : (1:ℝ) ≠ 0)
  filter_upwards [eventually_ge_atTop (1:ℕ),hb] with k hk hb
  dsimp only [c]
  apply (div_eq_iff (pow_ne_zero 2 hb)).mpr
  dsimp only
  rw [← pow_mul,← pow_add]
  congr 1
  omega

lemma scalar_factor (tau : ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)-2)*tau/(k:ℝ)) atTop (𝓝 tau) := by
  have hinv : Tendsto (fun k : ℕ => tau-2*tau/(k:ℝ)) atTop (𝓝 tau) := by
    have hd : Tendsto (fun k : ℕ => 2*tau/(k:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using (show Tendsto (fun _ : ℕ => tau) atTop (𝓝 tau) from tendsto_const_nhds).sub hd
  apply hinv.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
  have hn : (k:ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp
  <;> ring

theorem a_tendsto (tau : ℝ) : Tendsto (a tau) atTop (𝓝 ((1+tau)*limitC tau)) :=
  (tendsto_const_nhds.add (scalar_factor tau)).mul (c_tendsto tau)

theorem b_tendsto (tau : ℝ) : Tendsto (b tau) atTop (𝓝 (tau*limitC tau)) :=
  (scalar_factor tau).mul (c_tendsto tau)

theorem e_tendsto (tau : ℝ) :
    Tendsto (e tau) atTop (𝓝 (min ((1+tau)*limitC tau) (2*(tau*limitC tau)))) :=
  (a_tendsto tau).min (tendsto_const_nhds.mul (b_tendsto tau))

theorem threshold_tendsto (tau : ℝ) :
    Tendsto (threshold tau) atTop (𝓝 (limitThreshold tau)) := by
  have h := ((show Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2) from tendsto_const_nhds).mul (a_tendsto tau)).sub
    ((e_tendsto tau).div_atTop tendsto_natCast_atTop_atTop)
  unfold threshold limitThreshold
  simpa only [sub_zero,mul_assoc] using h

/-- The retained strong assumption is eventually true for every tau>0. -/
theorem strong_eventually (tau : ℝ) (ht : 0 < tau) :
    ∀ᶠ k : ℕ in atTop,1 ≤ ((k:ℝ)-2)*b tau k := by
  have hp : 0 < tau*limitC tau := mul_pos ht (Real.exp_pos _)
  have hb : ∀ᶠ k : ℕ in atTop,tau*limitC tau/2 ≤ b tau k :=
    (b_tendsto tau).eventually (eventually_ge_nhds (by linarith))
  have hk : ∀ᶠ k : ℕ in atTop,2+2/(tau*limitC tau) ≤ (k:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop).eventually (eventually_ge_atTop _)
  filter_upwards [hb,hk] with k hb hk
  have hdiv : 0 < 2/(tau*limitC tau) := by positivity
  have hprod : (2/(tau*limitC tau))*(tau*limitC tau)=2 := div_mul_cancel₀ 2 hp.ne'
  nlinarith [mul_nonneg (show 0 ≤ (k:ℝ)-2 by linarith) (show 0 ≤ b tau k-tau*limitC tau/2 by linarith)]

#print axioms log_one_sub_bound
#print axioms c_tendsto
#print axioms a_tendsto
#print axioms b_tendsto
#print axioms threshold_tendsto
#print axioms strong_eventually
end
end CIGAMF.P13.D6ScaledReferenceCoefficients
