import «LeanD6AllocationPhaseThreeParametersV1»
import «LeanD6AllocationMarginRegionV1»

/-! Feasibility of the phase-III small root. The explicit radical is compared
with a super-solution, allowing the true margin interval to be connected to the
all-distance certificate without assuming the optimizer formula is correct. -/
namespace CIGAMF.P13.D6AllocationPhaseThreeFeasible
open CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationMarginRegion CIGAMF.P13.D6ExpandedAllocation
noncomputable section

def marginHigh (q : ℝ) := Real.sqrt q/(1+Real.sqrt q)

theorem upper_endpoint_numerator (q mu : ℝ) (hq : 3 ≤ q)
    (hmu : 0 ≤ mu) (hu : mu ≤ marginHigh q) :
    mu ≤ 1 ∧ 0 ≤ q*(1-mu)^2-mu^2 := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have hd : 0 < 1+Real.sqrt q := by linarith
  have hline := (le_div_iff₀ hd).mp hu
  have hmu1 : mu ≤ 1 := by nlinarith
  have hprod : 0 ≤ Real.sqrt q*(1-mu) := mul_nonneg hs.le (by linarith)
  have he := Real.sq_sqrt (show 0 ≤ q by linarith)
  have hb : mu ≤ Real.sqrt q*(1-mu) := by nlinarith
  have hb2 := sq_le_sq₀ hmu hprod |>.mpr hb
  rw [mul_pow,he] at hb2
  exact ⟨hmu1,by linarith⟩

theorem shift_nonnegative (q mu : ℝ) (hq : 3 ≤ q)
    (hmu : 0 < mu) (hu : mu ≤ marginHigh q) : 0 ≤ shift q mu := by
  have hn := upper_endpoint_numerator q mu hq hmu.le hu
  have hd := radical_positive q mu hq hmu
  unfold shift
  exact div_nonneg hn.2 (add_nonneg
    (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith [hn.1])) hd.le)

/-- A super-solution bounds the smaller root, without any monotonicity assumption
on the quadratic outside its two roots. -/
theorem shift_le_of_supersolution (q mu x : ℝ) (hq : 3 ≤ q)
    (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hx : q*((1-mu)-(q-2)*x)^2-mu^2-(q-1)*x^2 ≤ 0) :
    shift q mu ≤ x := by
  have hk := K_pos q hq
  have hd := radical_positive q mu hq hmu
  have he := rationalized_shift q mu hq hmu hmu1
  have hs := radical_square q mu hq
  have hid : (q*(q-2)*(1-mu)-K q*x)^2-(D q mu)^2 =
      K q*(q*((1-mu)-(q-2)*x)^2-mu^2-(q-1)*x^2) := by
    rw [hs]
    unfold radicand K
    ring
  have hnon := mul_nonpos_of_nonneg_of_nonpos hk.le hx
  have hsq : (q*(q-2)*(1-mu)-K q*x)^2 ≤ (D q mu)^2 := by linarith [hid]
  have hlinear : q*(q-2)*(1-mu)-K q*x ≤ D q mu := by nlinarith [sq_nonneg (q*(q-2)*(1-mu)-K q*x-D q mu)]
  nlinarith

/-- The old exact boundary is a super-solution throughout phase III. -/
theorem shift_le_boundary_tilt (q mu : ℝ) (hq : 3 ≤ q)
    (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hlo : marginMax q ≤ mu) :
    shift q mu ≤ (1-mu)*tilt q := by
  have hr := radius_pos q hq
  have hz := tilt_pos q hq
  have hd : 0 < 1+radius q := by linarith
  have hline := (div_le_iff₀ hd).mp hlo
  have hnon : 0 ≤ (1-mu)*radius q := mul_nonneg (by linarith) hr.le
  have hbound : ((1-mu)*radius q)^2 ≤ mu^2 := by
    apply (sq_le_sq₀ hnon hmu.le).mpr
    nlinarith
  have hc := scale_properties q hq
  have hzbal := (root_properties q _ hq hc.1 hc.2.1 hc.2.2).2.2
  change (q+1)*(1-(q-2)*tilt q)^2=q*(1+tilt q)^2 at hzbal
  have hrbal := radius_balance q hq
  have hidentity : q*((1-mu)-(q-2)*((1-mu)*tilt q))^2-
      (q-1)*((1-mu)*tilt q)^2 = ((1-mu)*radius q)^2 := by
    have h1 := congrArg (fun t : ℝ => q*(1-mu)^2*t) hzbal
    have h2 := congrArg (fun t : ℝ => (1-mu)^2*t) hrbal
    unfold gain at h2
    have heq : (q+1)*(q*((1-mu)-(q-2)*((1-mu)*tilt q))^2-
        (q-1)*((1-mu)*tilt q)^2-((1-mu)*radius q)^2)=0 := by
      nlinarith [h1,h2]
    have := (mul_eq_zero.mp heq).resolve_left (by linarith : q+1 ≠ 0)
    linarith
  apply shift_le_of_supersolution q mu ((1-mu)*tilt q) hq hmu hmu1
  linarith [hidentity]

theorem marginMax_ge_half (q : ℝ) (hq : 3 ≤ q) : (1/2 : ℝ) ≤ marginMax q := by
  have hz := tilt_pos q hq
  have hqp : 0 < q+1 := by linarith
  have hb : (1 : ℝ) ≤ (q^2+2*q^2*tilt q+(tilt q)^2)/(q+1) := by
    apply (le_div_iff₀ hqp).mpr
    nlinarith [mul_nonneg (show 0 ≤ 2*q^2 by positivity) hz.le]
  have hr : (1 : ℝ) ≤ radius q := by
    have hs := Real.sqrt_le_sqrt hb
    simpa [radius] using hs
  unfold marginMax
  apply (le_div_iff₀ (by linarith : 0 < 1+radius q)).mpr
  linarith

theorem phase_shift_bounds (q mu : ℝ) (hq : 3 ≤ q)
    (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q) :
    (1/2 : ℝ) ≤ mu ∧ mu ≤ 1 ∧ 0 ≤ shift q mu ∧ 4*q*shift q mu ≤ 1-mu := by
  have hm := le_trans (marginMax_ge_half q hq) hlo
  have hmpos : 0 < mu := by linarith
  have hu := upper_endpoint_numerator q mu hq hmpos.le hup
  have hs := shift_le_boundary_tilt q mu hq hmpos hu.1 hlo
  have hc := scale_properties q hq
  have hz := (root_properties q _ hq hc.1 hc.2.1 hc.2.2).2.1
  change 4*q*tilt q ≤ 1 at hz
  have h1 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4*q by linarith)
  have h2 := mul_le_mul_of_nonneg_left hz (show 0 ≤ 1-mu by linarith [hu.1])
  exact ⟨hm,hu.1,shift_nonnegative q mu hq hmpos hup,by nlinarith [h1,h2]⟩

/-- The explicit phase-III weights are a probability mixture, uniformly in q. -/
theorem phase_mass_bounds (q mu : ℝ) (hq : 3 ≤ q)
    (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q) :
    0 ≤ mass q mu ∧ mass q mu ≤ 1/4 := by
  obtain ⟨hm,hm1,hs,hsmall⟩ := phase_shift_bounds q mu hq hlo hup
  have hmpos : 0 < mu := by linarith
  have hd := radical_positive q mu hq hmpos
  have hk := K_pos q hq
  have hr := rationalized_shift q mu hq hmpos hm1
  have hcpos : 0 ≤ K q+4*(q-1) := by linarith
  have hc : K q+4*(q-1) ≤ 4*q*(q*(q-2)) := by
    unfold K
    nlinarith [mul_nonneg (show 0 ≤ q-3 by linarith)
      (show 0 ≤ 3*q^2+5*q+8 by positivity)]
  have h1 := mul_le_mul_of_nonneg_left hsmall hcpos
  have h2 := mul_le_mul_of_nonneg_right hc (show 0 ≤ 1-mu by linarith)
  have hC : (K q+4*(q-1))*shift q mu ≤ q*(q-2)*(1-mu) := by
    apply le_of_mul_le_mul_left (a := 4*q) ?_ (by linarith)
    nlinarith [h1,h2]
  constructor
  · unfold mass
    exact div_nonneg (mul_nonneg (by linarith) hs) hd.le
  · unfold mass
    apply (div_le_iff₀ hd).mpr
    nlinarith [hC,hr]

/-- The distant-alternative guard now follows from the actual phase interval. -/
theorem phase_guard (q mu : ℝ) (hq : 3 ≤ q)
    (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q) :
    (q-1)*(shift q mu)^2 ≤ (1-2*mass q mu)*mu^2 := by
  obtain ⟨hm,hm1,hs,hsmall⟩ := phase_shift_bounds q mu hq hlo hup
  have hw := phase_mass_bounds q mu hq hlo hup
  have hsmall' : 4*q*shift q mu ≤ mu := by linarith
  have hsquare := (sq_le_sq₀ (show 0 ≤ 4*q*shift q mu by positivity)
    (show 0 ≤ mu by linarith)).mpr hsmall'
  have hc : 2*(q-1) ≤ (4*q)^2 := by nlinarith
  have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg (shift q mu))
  have hw' := mul_nonneg (show 0 ≤ 1/4-mass q mu by linarith [hw.2]) (sq_nonneg mu)
  nlinarith [hsquare,hc',hw']

theorem phase_all_distances_lower (q mu d u : ℝ) (hq : 3 ≤ q)
    (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hd : d=1 ∨ 2 ≤ d) (hdq : d ≤ q) :
    CIGAMF.P13.D6AllocationPhaseThreeCore.gammaTwice q mu (shift q mu) ≤
      CIGAMF.P13.D6AllocationPhaseThreeCore.mixedLoss q mu (mass q mu) d u := by
  have hm := phase_shift_bounds q mu hq hlo hup
  have hw := phase_mass_bounds q mu hq hlo hup
  exact CIGAMF.P13.D6AllocationPhaseThreeCore.all_distances_lower q mu (mass q mu)
    (shift q mu) d u hq hw.1 (by linarith [hw.2]) hd hdq
    (balance q mu hq (by linarith [hm.1]) hm.2.1)
    (stationarity q mu hq (by linarith [hm.1]) hm.2.1)
    (phase_guard q mu hq hlo hup)

#print axioms upper_endpoint_numerator
#print axioms shift_nonnegative
#print axioms shift_le_of_supersolution
#print axioms shift_le_boundary_tilt
#print axioms phase_shift_bounds
#print axioms phase_mass_bounds
#print axioms phase_guard
#print axioms phase_all_distances_lower
end
end CIGAMF.P13.D6AllocationPhaseThreeFeasible
