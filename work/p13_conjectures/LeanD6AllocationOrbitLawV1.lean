import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Dimension-parametric analytic certificate for the unknown-margin D6 design.
q=k-1>=3, true mu=1/2. This module proves the saddle-point polynomial law.
The finite permutation-orbit reduction from actual measurements is a separate
bridge; this module does not silently assume that bridge or algorithm optimality. -/
namespace CIGAMF.P13.D6AllocationOrbit

noncomputable def rootEquation (q z : ℝ) : ℝ :=
  ((q+1)*(q-2)^2-1)*z^2 - 2*(q+1)*(q-2)*z + 1

noncomputable def dualNumerator (q z s t : ℝ) : ℝ :=
  q*(q+1)*z^2*(t-1)^2 + 2*q*z*(1+z)*(t-1)*s -
    2*(q+1)*z*(1+z)*(t-1)*t + (1+z)^2*(q*s+(q+1)*t-2*s*t)

noncomputable def valueNumerator (q z : ℝ) : ℝ := q*(q+z^2)

/-- Every joint measurement orbit is dominated by the two allocated extremes.
The proof holds for real s,t over the entire triangle, not just finite counts. -/
theorem dual_triangle_bound (q z s t : ℝ) (hq : 3 ≤ q) (hz : 0 ≤ z)
    (hzsmall : (2*q+1)*z ≤ 1) (hroot : rootEquation q z = 0)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t ≤ q) :
    dualNumerator q z s t ≤ valueNumerator q z := by
  have hqt : 0 ≤ q-t := by linarith
  have hcz : 0 ≤ 2-(q-2)*z := by nlinarith
  have hC : 0 ≤ q*(q-3)*z^2+2-(4*q-2)*z := by
    have hprod : 0 ≤ q*(q-3)*z^2 := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg z)
    nlinarith
  have h0id : valueNumerator q z - dualNumerator q z 0 t =
      (q+1)*(q-t)*z*(2-(q-2)*z)*(q*(q-3)+q-t) +
        ((q+1)*(q-t)-q)*rootEquation q z := by
    unfold valueNumerator dualNumerator rootEquation
    ring
  have h0 : dualNumerator q z 0 t ≤ valueNumerator q z := by
    rw [hroot, mul_zero, add_zero] at h0id
    have hh : 0 ≤ (q+1)*(q-t)*z*(2-(q-2)*z)*(q*(q-3)+q-t) := by
      apply mul_nonneg
      · exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hqt) hz) hcz
      · have : 0 ≤ q*(q-3) := mul_nonneg (by linarith) (by linarith)
        linarith
    linarith
  have h1id : valueNumerator q z - dualNumerator q z (q-t) t =
      t*(q-t)*(q*(q-3)*z^2+2-(4*q-2)*z)-t*rootEquation q z := by
    unfold valueNumerator dualNumerator rootEquation
    ring
  have h1 : dualNumerator q z (q-t) t ≤ valueNumerator q z := by
    rw [hroot, mul_zero, sub_zero] at h1id
    have hh := mul_nonneg (mul_nonneg ht hqt) hC
    linarith
  have hid : (q-t)*(valueNumerator q z-dualNumerator q z s t) =
      (q-t-s)*(valueNumerator q z-dualNumerator q z 0 t) +
      s*(valueNumerator q z-dualNumerator q z (q-t) t) := by
    unfold valueNumerator dualNumerator
    ring
  by_cases hzero : q-t=0
  · have hs0 : s=0 := by linarith
    simpa [hs0] using h0
  · have hp : 0 < q-t := lt_of_le_of_ne hqt (Ne.symm hzero)
    have hl := mul_nonneg (show 0 ≤ q-t-s by linarith) (sub_nonneg.mpr h0)
    have hr := mul_nonneg hs (sub_nonneg.mpr h1)
    nlinarith

noncomputable def calibrationRoot (q : ℝ) : ℝ :=
  1 / ((q+1)*(q-2) + Real.sqrt (q*(q+1)*(q-2)^2+1))

/-- The explicit algebraic root lies in the branch needed by the certificate. -/
theorem calibrationRoot_properties (q : ℝ) (hq : 3 ≤ q) :
    0 < calibrationRoot q ∧ (2*q+1)*calibrationRoot q ≤ 1 ∧
      rootEquation q (calibrationRoot q) = 0 := by
  let R := Real.sqrt (q*(q+1)*(q-2)^2+1)
  have hx : 0 ≤ q*(q+1)*(q-2)^2+1 := by positivity
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R^2 = q*(q+1)*(q-2)^2+1 := Real.sq_sqrt hx
  have hqpos : 0 < q := by linarith
  have hqminus : 0 < q-2 := by linarith
  have hRlower : q*(q-2) ≤ R := by
    have hp : 0 ≤ q*(q-2) := by positivity
    have hdiff : (q*(q-2))^2 ≤ R^2 := by
      rw [hRsq]
      nlinarith [sq_nonneg (q-2)]
    nlinarith
  have hd : 0 < (q+1)*(q-2)+R := by positivity
  have hds : 2*q+1 ≤ (q+1)*(q-2)+R := by
    nlinarith [mul_nonneg (show 0 ≤ 2*q+1 by linarith) (show 0 ≤ q-3 by linarith)]
  change 0 < 1/((q+1)*(q-2)+R) ∧
    (2*q+1)*(1/((q+1)*(q-2)+R)) ≤ 1 ∧
    rootEquation q (1/((q+1)*(q-2)+R)) = 0
  refine ⟨one_div_pos.mpr hd, ?_, ?_⟩
  · rw [mul_one_div, div_le_one hd]
    exact hds
  · unfold rootEquation
    field_simp
    nlinarith [hRsq]

/-- Closed form valid for every width k=q+1>=4, not fitted to m=10. -/
theorem all_width_joint_dual (q s t : ℝ) (hq : 3 ≤ q)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t ≤ q) :
    dualNumerator q (calibrationRoot q) s t ≤ valueNumerator q (calibrationRoot q) := by
  have h := calibrationRoot_properties q hq
  exact dual_triangle_bound q _ s t hq h.1.le h.2.1 h.2.2 hs ht hst

#print axioms dual_triangle_bound
#print axioms calibrationRoot_properties
#print axioms all_width_joint_dual

noncomputable def calibrationWeight (q z : ℝ) : ℝ :=
  z / ((q+1)*(q-2)*(1-(q-2)*z)+z)

noncomputable def primalA (q t : ℝ) : ℝ := (q+(t-1)^2)/(q+1)
noncomputable def primalB (q t : ℝ) : ℝ := ((q-1)-(q-2)*t)^2
noncomputable def normalizedValue (q z : ℝ) : ℝ := (q+z^2)/(q+1)

/-- The small calibration mass is positive, and leaves enough probability on
A-queries to reject every alternative at exchange distance >=2. -/
theorem calibrationWeight_properties (q z : ℝ) (hq : 3 ≤ q) (hz : 0 < z)
    (hsmall : (2*q+1)*z ≤ 1) :
    0 < calibrationWeight q z ∧ calibrationWeight q z < 1 ∧
    calibrationWeight q z*(q+1)*(q-2)*(1-(q-2)*z) =
      (1-calibrationWeight q z)*z ∧
    normalizedValue q z ≤ 1-calibrationWeight q z := by
  let E := (q+1)*(q-2)*(1-(q-2)*z)+z
  have hz3 : z ≤ 1/3 := by nlinarith
  have hcz : 0 ≤ (q-2)*z := mul_nonneg (by linarith) hz.le
  have hczhalf : (q-2)*z ≤ 1/2 := by nlinarith
  have hc : 1 ≤ q-2 := by linarith
  have hk : 0 < q+1 := by linarith
  have hterm : (q+1)/2 ≤ (q+1)*(q-2)*(1-(q-2)*z) := by
    have h1 : 1/2 ≤ (q-2)*(1-(q-2)*z) := by
      nlinarith [mul_nonneg (show 0 ≤ q-3 by linarith) (show 0 ≤ 1-(q-2)*z by linarith)]
    nlinarith
  have hE : 0 < E := by dsimp [E]; linarith
  change 0 < z/E ∧ z/E < 1 ∧
    (z/E)*(q+1)*(q-2)*(1-(q-2)*z) = (1-z/E)*z ∧ normalizedValue q z ≤ 1-z/E
  refine ⟨div_pos hz hE, (div_lt_one hE).mpr (by dsimp [E]; linarith), ?_, ?_⟩
  · have hid : (z/E)*E = z := div_mul_cancel₀ z (ne_of_gt hE)
    have hsplit : (z/E)*(q+1)*(q-2)*(1-(q-2)*z) + (z/E)*z = z := by
      calc
        _ = (z/E)*E := by dsimp [E]; ring
        _ = z := hid
    linarith
  · have hweight : (q+1)*(z/E) ≤ 2*z := by
      rw [← mul_div_assoc, div_le_iff₀ hE]
      dsimp [E]
      nlinarith
    unfold normalizedValue
    apply (div_le_iff₀ hk).mpr
    nlinarith [sq_nonneg z, mul_nonneg hz.le (show 0 ≤ 1/3-z by linarith)]

/-- Completed square for the two-orbit design, with every real nuisance value.
The stationarity equality is proved by calibrationWeight_properties. -/
theorem primal_square_identity (q z w t : ℝ) (hq : q+1 ≠ 0)
    (hroot : rootEquation q z = 0)
    (hstat : w*(q+1)*(q-2)*(1-(q-2)*z) = (1-w)*z) :
    (q+1)*((1-w)*primalA q t+w*primalB q t-normalizedValue q z) =
      ((1-w)+w*(q+1)*(q-2)^2)*(t-1-z)^2 := by
  unfold primalA primalB normalizedValue
  field_simp
  have hid : (1-w)*(q+(t-1)^2)+w*(q+1)*((q-1)-(q-2)*t)^2-(q+z^2) -
      ((1-w)+w*(q+1)*(q-2)^2)*(t-1-z)^2 =
      w*rootEquation q z - 2*(t-1-z)*(w*(q+1)*(q-2)*(1-(q-2)*z)-(1-w)*z) := by
    unfold rootEquation
    ring
  rw [hroot, hstat] at hid
  nlinarith

/-- All nuisance alternatives at nearest exchange distance are rejected at
at least the proposed information rate by this explicit mixture. -/
theorem all_width_primal_lower (q t : ℝ) (hq : 3 ≤ q) :
    normalizedValue q (calibrationRoot q) ≤
      (1-calibrationWeight q (calibrationRoot q))*primalA q t +
        calibrationWeight q (calibrationRoot q)*primalB q t := by
  have hz := calibrationRoot_properties q hq
  have hw := calibrationWeight_properties q _ hq hz.1 hz.2.1
  have hid := primal_square_identity q (calibrationRoot q) (calibrationWeight q (calibrationRoot q))
    t (by linarith) hz.2.2 hw.2.2.1
  have hcoef : 0 ≤ (1-calibrationWeight q (calibrationRoot q)) +
      calibrationWeight q (calibrationRoot q)*(q+1)*(q-2)^2 := by
    have hprod : 0 ≤ calibrationWeight q (calibrationRoot q)*(q+1)*(q-2)^2 :=
      mul_nonneg (mul_nonneg hw.1.le (by linarith)) (sq_nonneg _)
    linarith [hw.2.1]
  have hprod := mul_nonneg hcoef (sq_nonneg (t-1-calibrationRoot q))
  nlinarith

#print axioms calibrationWeight_properties
#print axioms primal_square_identity
#print axioms all_width_primal_lower

/-- The same dual also bounds every scalar Q measurement, including Q_j. -/
theorem all_width_scalar_dual (q : ℝ) (hq : 3 ≤ q) :
    (1-calibrationRoot q)^2/(q+1) ≤ normalizedValue q (calibrationRoot q) ∧
    (1+(q-1)*(calibrationRoot q)^2)/q ≤ normalizedValue q (calibrationRoot q) ∧
    (calibrationRoot q)^2 ≤ normalizedValue q (calibrationRoot q) := by
  let z := calibrationRoot q
  have hz := calibrationRoot_properties q hq
  have hzpos : 0 < z := hz.1
  have hzsmall : (2*q+1)*z ≤ 1 := hz.2.1
  have hzle : z ≤ 1 := by nlinarith
  have hsq : z^2 ≤ 1 := by nlinarith
  have hp : 0 < q := by linarith
  have hk : 0 < q+1 := by linarith
  change (1-z)^2/(q+1) ≤ (q+z^2)/(q+1) ∧
    (1+(q-1)*z^2)/q ≤ (q+z^2)/(q+1) ∧ z^2 ≤ (q+z^2)/(q+1)
  refine ⟨(div_le_div_iff_of_pos_right hk).mpr (by nlinarith), ?_, ?_⟩
  · apply (div_le_div_iff₀ hp hk).mpr
    have hc : 0 ≤ q^2-q-1 := by nlinarith
    have hh := mul_nonneg hc (show 0 ≤ 1-z^2 by linarith)
    nlinarith
  · apply (le_div_iff₀ hk).mpr
    have hh := mul_nonneg hp.le (show 0 ≤ 1-z^2 by linarith)
    nlinarith

/-- A feasible nuisance value attains the lower bound: nu=(1+z)/2. -/
theorem all_width_primal_attainment (q : ℝ) (hq : 3 ≤ q) :
    0 ≤ (1+calibrationRoot q)/2 ∧ (1+calibrationRoot q)/2 ≤ 1 ∧
    (1-calibrationWeight q (calibrationRoot q))*primalA q (1+calibrationRoot q) +
      calibrationWeight q (calibrationRoot q)*primalB q (1+calibrationRoot q) =
        normalizedValue q (calibrationRoot q) := by
  have hz := calibrationRoot_properties q hq
  have hw := calibrationWeight_properties q _ hq hz.1 hz.2.1
  have hid := primal_square_identity q (calibrationRoot q) (calibrationWeight q (calibrationRoot q))
    (1+calibrationRoot q) (by linarith) hz.2.2 hw.2.2.1
  have hzero : 1+calibrationRoot q-1-calibrationRoot q = 0 := by ring
  rw [hzero] at hid
  norm_num at hid
  refine ⟨by linarith [hz.1], ?_, ?_⟩
  · nlinarith [hz.1, hz.2.1]
  · rcases hid with hf | ht
    · linarith
    · linarith

/-- Distant alternatives are covered whenever their normalized A-query loss
is at least one, as occurs for exchange distance at least two. -/
theorem all_width_distant_lower (q a b : ℝ) (hq : 3 ≤ q) (ha : 1 ≤ a) (hb : 0 ≤ b) :
    normalizedValue q (calibrationRoot q) ≤
      (1-calibrationWeight q (calibrationRoot q))*a +
        calibrationWeight q (calibrationRoot q)*b := by
  have hz := calibrationRoot_properties q hq
  have hw := calibrationWeight_properties q _ hq hz.1 hz.2.1
  have hA := mul_nonneg (show 0 ≤ 1-calibrationWeight q (calibrationRoot q) by linarith [hw.2.1])
    (show 0 ≤ a-1 by linarith)
  have hB := mul_nonneg hw.1.le hb
  linarith [hw.2.2.2]

#print axioms all_width_scalar_dual
#print axioms all_width_primal_attainment
#print axioms all_width_distant_lower
end CIGAMF.P13.D6AllocationOrbit
