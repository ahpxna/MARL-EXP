import «LeanD6ScaledReferenceErrorV1»
import «LeanD6ScaledReferencePhaseV1»

/-! Explicit finite error for the clamped static value; no asymptotic premise. -/
namespace CIGAMF.P13.D6ScaledValueError
open CIGAMF.P13.D6ScaledReferenceCoefficients CIGAMF.P13.D6ScaledReferenceError
open CIGAMF.P13.D6ScaledReferencePhase
noncomputable section

def D (tau : ℝ) := 2*tau+4*tau^2
def Da (tau : ℝ) := (1+tau)*D tau+2*tau
def Db (tau : ℝ) := tau*D tau+2*tau
def Dt (tau : ℝ) := 2*Da tau+(1+tau)
def Nv (tau : ℝ) := 2*(1+tau)*(2*Db tau+4)+(2+2*tau)*Dt tau
def Cv (tau : ℝ) := Nv tau/(2*limitC tau)+2*(1+tau)^2*D tau/(limitC tau)^2

lemma abs_difference (x y : ℝ) : |x-y| ≤ |x|+|y| := by
  simpa only [sub_eq_add_neg,abs_neg] using abs_add_le x (-y)

lemma product_error (x y X Y ex ey bx bY : ℝ)
    (hx : |x-X| ≤ ex) (hy : |y-Y| ≤ ey) (hb : |x| ≤ bx) (hB : |Y| ≤ bY) :
    |x*y-X*Y| ≤ bx*ey+ex*bY := by
  have hbx : 0 ≤ bx := (abs_nonneg _).trans hb
  have hex : 0 ≤ ex := (abs_nonneg _).trans hx
  calc
    |x*y-X*Y|=|x*(y-Y)+(x-X)*Y| := by congr 1;ring
    _ ≤ |x*(y-Y)|+|(x-X)*Y| := abs_add_le _ _
    _ = |x| *|y-Y|+|x-X| *|Y| := by rw [abs_mul,abs_mul]
    _ ≤ bx*ey+ex*bY := by gcongr

lemma coefficients (tau : ℝ) (ht : 0 ≤ tau) (k : ℕ) (hk : 2 ≤ k)
    (hkt : 2*tau ≤ (k:ℝ)) :
    0 ≤ c tau k ∧ c tau k ≤ 1 ∧
    0 ≤ a tau k ∧ a tau k ≤ 1+tau ∧
    0 ≤ b tau k ∧ b tau k ≤ tau ∧
    |a tau k-(1+tau)*limitC tau| ≤ Da tau/(k:ℝ) ∧
    |b tau k-tau*limitC tau| ≤ Db tau/(k:ℝ) := by
  have hkp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hx : 0 ≤ tau/(k:ℝ) := div_nonneg ht hkp.le
  have hx1 : tau/(k:ℝ) ≤ 1/2 := (div_le_iff₀ hkp).mpr (by linarith)
  have hc0 : 0 ≤ c tau k := pow_nonneg (by linarith) _
  have hc1 : c tau k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hb0 : 0 ≤ b tau k := by unfold b;positivity
  have hidb : b tau k=tau*c tau k-2*tau*c tau k/(k:ℝ) := by unfold b;field_simp <;> ring
  have hida : a tau k=(1+tau)*c tau k-2*tau*c tau k/(k:ℝ) := by unfold a;field_simp <;> ring
  have ha0 : 0 ≤ a tau k := by unfold a;positivity
  have hcprod : 0 ≤ 2*tau*c tau k/(k:ℝ) := by positivity
  have hb1 : b tau k ≤ tau := by rw [hidb];nlinarith
  have ha1 : a tau k ≤ 1+tau := by rw [hida];nlinarith
  have hc := coefficient_error tau ht k (by omega) hkt
  have hrem : |2*tau*c tau k/(k:ℝ)| ≤ 2*tau/(k:ℝ) := by
    rw [abs_of_nonneg hcprod]
    exact div_le_div_of_nonneg_right (by nlinarith) hkp.le
  refine ⟨hc0,hc1,ha0,ha1,hb0,hb1,?_,?_⟩
  · have hid : a tau k-(1+tau)*limitC tau=(1+tau)*(c tau k-limitC tau)-2*tau*c tau k/(k:ℝ) := by rw [hida];ring
    rw [hid]
    have htri := abs_difference ((1+tau)*(c tau k-limitC tau)) (2*tau*c tau k/(k:ℝ))
    rw [abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1+tau)] at htri
    have hm := mul_le_mul_of_nonneg_left hc (by linarith : 0 ≤ 1+tau)
    dsimp [Da,D]
    calc
      _ ≤ (1+tau)*((2*tau+4*tau^2)/(k:ℝ))+2*tau/(k:ℝ) := by linarith
      _ = _ := by ring
  · have hid : b tau k-tau*limitC tau=tau*(c tau k-limitC tau)-2*tau*c tau k/(k:ℝ) := by rw [hidb];ring
    rw [hid]
    have htri := abs_difference (tau*(c tau k-limitC tau)) (2*tau*c tau k/(k:ℝ))
    rw [abs_mul,abs_of_nonneg ht] at htri
    have hm := mul_le_mul_of_nonneg_left hc ht
    dsimp [Db,D]
    calc
      _ ≤ tau*((2*tau+4*tau^2)/(k:ℝ))+2*tau/(k:ℝ) := by linarith
      _ = _ := by ring

lemma threshold_error (tau : ℝ) (ht : 0 ≤ tau) (k : ℕ) (hk : 2 ≤ k)
    (hkt : 2*tau ≤ (k:ℝ)) :
    |threshold tau k-limitThreshold tau| ≤ Dt tau/(k:ℝ) := by
  obtain ⟨hc0,hc1,ha0,ha1,hb0,hb1,hea,heb⟩ := coefficients tau ht k hk hkt
  have he0 : 0 ≤ e tau k := le_min ha0 (by positivity)
  have he1 : e tau k ≤ 1+tau := (min_le_left _ _).trans ha1
  have he : |e tau k/(k:ℝ)| ≤ (1+tau)/(k:ℝ) := by rw [abs_of_nonneg (by positivity)];gcongr
  have h := abs_difference (2*(a tau k-(1+tau)*limitC tau)) (e tau k/(k:ℝ))
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  have hid : threshold tau k-limitThreshold tau=2*(a tau k-(1+tau)*limitC tau)-e tau k/(k:ℝ) := by unfold threshold limitThreshold;ring
  rw [hid]
  calc
    _ ≤ 2*(Da tau/(k:ℝ))+(1+tau)/(k:ℝ) := by linarith
    _ = Dt tau/(k:ℝ) := by unfold Dt;ring

lemma quotient_error (N C n c E D : ℝ) (hC : 0<C) (hc : C/2 ≤ c)
    (hn : |n-N| ≤ E) (hd : |c-C| ≤ D) :
    |n/(4*c)-N/(4*C)| ≤ E/(2*C)+|N| *D/(2*C^2) := by
  have hcp : 0<c := by linarith
  have hE : 0 ≤ E := (abs_nonneg _).trans hn
  have hD : 0 ≤ D := (abs_nonneg _).trans hd
  have hid : n/(4*c)-N/(4*C)=(n-N)/(4*c)+N*(C-c)/(4*c*C) := by field_simp;ring
  rw [hid]
  calc
    _ ≤ |(n-N)/(4*c)|+|N*(C-c)/(4*c*C)| := abs_add_le _ _
    _ = |n-N|/(4*c)+|N| *|c-C|/(4*c*C) := by simp only [abs_div,abs_mul,abs_of_pos hcp,abs_of_pos hC,abs_of_pos (by norm_num : (0:ℝ)<4),abs_sub_comm C c]
    _ ≤ E/(4*c)+|N| *D/(4*c*C) := by gcongr
    _ ≤ E/(2*C)+|N| *D/(2*C^2) := by
      apply add_le_add
      · apply div_le_div_of_nonneg_left hE (by positivity);linarith
      · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith

/-- The normalized phase value has explicit O(1/k) error. The last condition
is a numeric size threshold ensuring that its denominator stays positive. -/
theorem finite_value_error (tau rho : ℝ) (ht : 0 ≤ tau) (hr : 1 ≤ rho) (hr2 : rho ≤ 2)
    (k : ℕ) (hk : 2 ≤ k) (hkt : 2*tau ≤ (k:ℝ))
    (hlarge : 2*D tau/(k:ℝ) ≤ limitC tau) :
    |value tau rho k/(k:ℝ)-limitValue tau rho| ≤ Cv tau/(k:ℝ) := by
  have hkp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hk2 : (2:ℝ)≤k := by exact_mod_cast hk
  have hC : 0<limitC tau := Real.exp_pos _
  have hC1 : limitC tau ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨hc0,hc1,ha0,ha1,hb0,hb1,hea,heb⟩ := coefficients tau ht k hk hkt
  have he0 : 0 ≤ e tau k := le_min ha0 (by positivity)
  have he1 : e tau k ≤ a tau k := min_le_left _ _
  have hce : |c tau k-limitC tau| ≤ D tau/(k:ℝ) := coefficient_error tau ht k (by omega) hkt
  have hcl : limitC tau/2 ≤ c tau k := by
    have := (abs_le.mp hce).1
    rw [mul_div_assoc] at hlarge
    linarith
  let f := max 0 (threshold tau k-rho)
  let F := max 0 (limitThreshold tau-rho)
  let u := max 0 (e tau k-(2*a tau k-rho))/((k:ℝ)-1)
  have hk1 : (0:ℝ) ≤ (k:ℝ)-1 := by linarith
  have hD : 0 ≤ D tau := by unfold D;positivity
  have hu0 : 0 ≤ u := div_nonneg (le_max_left _ _) hk1
  have hu : u ≤ 4/(k:ℝ) := by
    have hm : max 0 (e tau k-(2*a tau k-rho)) ≤ 2 := max_le (by norm_num) (by linarith)
    calc
      u ≤ 2/((k:ℝ)-1) := by dsimp [u];gcongr
      _ ≤ 4/(k:ℝ) := by apply (div_le_div_iff₀ (by linarith) hkp).mpr;linarith
  have hf : |f| ≤ 2*(1+tau) := by
    rw [abs_of_nonneg (le_max_left _ _)]
    apply max_le (by positivity)
    dsimp [threshold]
    have : 0 ≤ e tau k/(k:ℝ) := by positivity
    linarith
  have hF : |F| ≤ 2*(1+tau) := by
    rw [abs_of_nonneg (le_max_left _ _)]
    apply max_le (by positivity)
    dsimp [limitThreshold]
    nlinarith
  have hfe : |f-F| ≤ Dt tau/(k:ℝ) := by
    have h := abs_max_sub_max_le_max (0:ℝ) (threshold tau k-rho) 0 (limitThreshold tau-rho)
    simp only [sub_self,abs_zero,sub_sub_sub_cancel_right,max_eq_right (abs_nonneg (threshold tau k-limitThreshold tau))] at h
    exact h.trans (threshold_error tau ht k hk hkt)
  have hp : |rho-2*tau*limitC tau| ≤ 2+2*tau := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hpe : |(rho-2*b tau k+u)-(rho-2*tau*limitC tau)| ≤ (2*Db tau+4)/(k:ℝ) := by
    have hid : (rho-2*b tau k+u)-(rho-2*tau*limitC tau)=(-2)*(b tau k-tau*limitC tau)+u := by ring
    rw [hid]
    have h := abs_add_le ((-2)*(b tau k-tau*limitC tau)) u
    rw [abs_mul,abs_of_nonneg hu0] at h
    rw [show |(-2:ℝ)|=2 by norm_num] at h
    calc
      _ ≤ 2*(Db tau/(k:ℝ))+4/(k:ℝ) := by linarith
      _ = _ := by ring
  have hn := product_error f (rho-2*b tau k+u) F (rho-2*tau*limitC tau)
    (Dt tau/(k:ℝ)) ((2*Db tau+4)/(k:ℝ)) (2*(1+tau)) (2+2*tau) hfe hpe hf hp
  have hn' : |f*(rho-2*b tau k+u)-F*(rho-2*tau*limitC tau)| ≤ Nv tau/(k:ℝ) := by
    convert hn using 1 <;> unfold Nv <;> ring
  have hN : |F*(rho-2*tau*limitC tau)| ≤ 4*(1+tau)^2 := by
    rw [abs_mul]
    calc
      _ ≤ (2*(1+tau))*(2+2*tau) := by gcongr
      _ = _ := by ring
  have hq := quotient_error (F*(rho-2*tau*limitC tau)) (limitC tau)
    (f*(rho-2*b tau k+u)) (c tau k) (Nv tau/(k:ℝ)) (D tau/(k:ℝ)) hC hcl hn' hce
  have hv : value tau rho k/(k:ℝ)=f*(rho-2*b tau k+u)/(4*c tau k) := by
    rw [value,normalized_value _ _ _ _ _ (by linarith)]
    dsimp [f,u,threshold]
    congr 3
    ring
  rw [hv]
  change |f*(rho-2*b tau k+u)/(4*c tau k)-F*(rho-2*tau*limitC tau)/(4*limitC tau)| ≤ _
  calc
    _ ≤ (Nv tau/(k:ℝ))/(2*limitC tau)+|F*(rho-2*tau*limitC tau)| *(D tau/(k:ℝ))/(2*(limitC tau)^2) := hq
    _ ≤ (Nv tau/(k:ℝ))/(2*limitC tau)+(4*(1+tau)^2)*(D tau/(k:ℝ))/(2*(limitC tau)^2) := by
      gcongr
    _ = Cv tau/(k:ℝ) := by unfold Cv;ring

#print axioms coefficients
#print axioms threshold_error
#print axioms quotient_error
#print axioms finite_value_error
end
end CIGAMF.P13.D6ScaledValueError
