import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Analytic certificate for the larger D6 measurement library: both j-on and
j-off groups of size <=q=k-1. True margin is 1/2. Values below are normalized
by eight, so actual variance-one Gaussian KL is `value / 8`.
This file proves the dimension-parametric algebra. The finite averaging bridge
from actual worlds is separately exact-checked, not assumed formalized here. -/
namespace CIGAMF.P13.D6ExpandedAllocation

noncomputable def scale (q : ℝ) : ℝ := Real.sqrt (q/(q+1))
noncomputable def weight (q c : ℝ) : ℝ := c/(q-2+c)
noncomputable def target (q c : ℝ) : ℝ := (q-1)/(q-2+c)
noncomputable def value (q c : ℝ) : ℝ := (c*(q-1)/(q-2+c))^2
noncomputable def designLoss (q c d t : ℝ) : ℝ :=
  (1-weight q c)*(d*(d*(q-1)+1)/(q+1))*t^2 +
    weight q c*((q-1)-(q-d-1)*t)^2

/-- The closed-form scale has no fitted or dimension-specific constants. -/
theorem scale_properties (q : ℝ) (hq : 3 ≤ q) :
    3/4 ≤ scale q ∧ scale q < 1 ∧ (q+1)*(scale q)^2=q := by
  have hp : 0 < q := by linarith
  have hk : 0 < q+1 := by linarith
  have hsq : (scale q)^2 = q/(q+1) := Real.sq_sqrt (div_nonneg hp.le hk.le)
  have heq : (q+1)*(scale q)^2 = q := by
    nlinarith [(eq_div_iff (ne_of_gt hk)).mp hsq]
  have hnonneg : 0 ≤ scale q := Real.sqrt_nonneg _
  have hlt : q/(q+1) < 1 := (div_lt_one hk).mpr (by linarith)
  have hlo : (3/4 : ℝ) ≤ q/(q+1) := (le_div_iff₀ hk).mpr (by linarith)
  exact ⟨by nlinarith, by nlinarith, heq⟩

/-- Explicit mixture and least-favourable nuisance parameter are feasible. -/
theorem parameters (q c : ℝ) (hq : 3 ≤ q) (hc : 3/4 ≤ c) (hc1 : c < 1) :
    0 < weight q c ∧ weight q c < 1 ∧ 0 ≤ target q c/2 ∧ target q c/2 ≤ 1 := by
  have hd : 0 < q-2+c := by linarith
  unfold weight target
  refine ⟨div_pos (by linarith) hd, (div_lt_one hd).mpr (by linarith), ?_, ?_⟩
  · exact div_nonneg (div_nonneg (by linarith) hd.le) (by norm_num)
  · have hh : (q-1)/(q-2+c) ≤ 2 := (div_le_iff₀ hd).mpr (by linarith)
    linarith

/-- Completed square of the two allocated query orbits at exchange distance
one. It is valid for every real nuisance value, without a parameter grid. -/
theorem nearest_completed_square (q c t : ℝ) (hq : 3 ≤ q) (hc : 0 < c)
    (hscale : (q+1)*c^2=q) :
    designLoss q c 1 t = value q c+c*(q-2)*(t-target q c)^2 := by
  have hd : q-2+c ≠ 0 := ne_of_gt (show 0 < q-2+c by linarith)
  have hk : q+1 ≠ 0 := by linarith
  have hcoef : (1*(1*(q-1)+1)/(q+1)) = c^2 := by
    apply (div_eq_iff hk).mpr
    nlinarith [hscale]
  unfold designLoss
  rw [hcoef]
  unfold weight value target
  field_simp [hd]
  ring

/-- The primal design rejects every nearest alternative at the proposed rate. -/
theorem nearest_lower (q t : ℝ) (hq : 3 ≤ q) :
    value q (scale q) ≤ designLoss q (scale q) 1 t := by
  have hc := scale_properties q hq
  rw [nearest_completed_square q _ t hq (by linarith [hc.1]) hc.2.2]
  have hp := mul_nonneg (mul_nonneg (show 0 ≤ scale q by linarith [hc.1])
    (show 0 ≤ q-2 by linarith)) (sq_nonneg (t-target q (scale q)))
  linarith

/-- The same explicit value is attained by a feasible nuisance parameter. -/
theorem nearest_attainment (q : ℝ) (hq : 3 ≤ q) :
    designLoss q (scale q) 1 (target q (scale q)) = value q (scale q) := by
  have hc := scale_properties q hq
  rw [nearest_completed_square q _ _ hq (by linarith [hc.1]) hc.2.2]
  simp

/-- The coefficient inequality needed for every exchange distance, proved on
the full real interval [1,q], hence also for all legal integer distances. -/
theorem distance_coefficient (q d : ℝ) (hq : 3 ≤ q) (hd : 1 ≤ d) (hdq : d ≤ q) :
    q*(q-d-1)^2 ≤ d*(d*(q-1)+1)*(q-2)^2 := by
  have h1 : 0 ≤ d*(q-3)*(q-1)^2 := by positivity
  have h2 : q ≤ q*(q-1)^2 := by nlinarith [mul_nonneg (show 0 ≤ q by linarith) (show 0 ≤ (q-1)^2-1 by nlinarith)]
  have hp := mul_nonneg (show 0 ≤ d-1 by linarith)
    (show 0 ≤ d*(q-3)*(q-1)^2+q*(q-1)^2-d by linarith)
  have hid : d*(d*(q-1)+1)*(q-2)^2-q*(q-d-1)^2 =
      (d-1)*(d*(q-3)*(q-1)^2+q*(q-1)^2-d) := by ring
  linarith

/-- Scaled adjacent-alternative average for a query with s coordinates in A,
t coordinates in B, and distinguished-coordinate switch h in {0,1}. -/
noncomputable def dual (q z h s t : ℝ) : ℝ :=
  q*(q+1)*z^2*(t-h)^2+2*q*z*(1+z)*(t-h)*s-
    2*(q+1)*z*(1+z)*(t-h)*t+(1+z)^2*(q*s+(q+1)*t-2*s*t)

/-- A general endpoint envelope, stronger than checking finitely many group
sizes. The switch can vary continuously over [0,1]. -/
theorem dual_envelope (q z h s t V : ℝ) (hq : 3 ≤ q) (hz : 0 ≤ z)
    (hzsmall : 4*q*z ≤ 1) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t ≤ q)
    (hA : dual q z h q 0 ≤ V) (hB : dual q z h 0 q ≤ V) :
    dual q z h s t ≤ V := by
  have hqt : 0 ≤ q-t := by linarith
  have hC : 0 ≤ q*(q-3)*z^2+2-(4*q-2)*z := by
    have hp : 0 ≤ q*(q-3)*z^2 := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg z)
    nlinarith
  have hM : 0 ≤ q*z^2*(q+t-2*h)-2*z*(1+z)*(q+t-h)+(1+z)^2 := by
    have h1 := mul_nonneg (show 0 ≤ q*z^2 by positivity) (show 0 ≤ q+t-2*h by linarith)
    have h2 := mul_nonneg (show 0 ≤ 2*z*(1+z) by positivity) (show 0 ≤ 2*q-(q+t-h) by linarith)
    have h3 := mul_nonneg (show 0 ≤ 1+z by linarith) (show 0 ≤ 1+z-4*q*z by linarith)
    nlinarith
  have h0id : dual q z h 0 q-dual q z h 0 t =
      (q+1)*(q-t)*(q*z^2*(q+t-2*h)-2*z*(1+z)*(q+t-h)+(1+z)^2) := by
    unfold dual; ring
  have h0 : dual q z h 0 t ≤ V := by
    have hp := mul_nonneg (mul_nonneg (show 0 ≤ q+1 by linarith) hqt) hM
    linarith
  have hdiag : q*(V-dual q z h (q-t) t) =
      (q-t)*(V-dual q z h q 0)+t*(V-dual q z h 0 q)+
        q*t*(q-t)*(q*(q-3)*z^2+2-(4*q-2)*z) := by unfold dual; ring
  have h1 : dual q z h (q-t) t ≤ V := by
    have ha := mul_nonneg hqt (sub_nonneg.mpr hA)
    have hb := mul_nonneg ht (sub_nonneg.mpr hB)
    have hc := mul_nonneg (mul_nonneg (mul_nonneg (show 0 ≤ q by linarith) ht) hqt) hC
    nlinarith
  have hid : (q-t)*(V-dual q z h s t) =
      (q-t-s)*(V-dual q z h 0 t)+s*(V-dual q z h (q-t) t) := by unfold dual; ring
  by_cases hzero : q-t=0
  · have hs0 : s=0 := by linarith
    simpa [hs0] using h0
  · have hp : 0 < q-t := lt_of_le_of_ne hqt (Ne.symm hzero)
    have hl := mul_nonneg (show 0 ≤ q-t-s by linarith) (sub_nonneg.mpr h0)
    have hr := mul_nonneg hs (sub_nonneg.mpr h1)
    nlinarith

#print axioms scale_properties
#print axioms parameters
#print axioms nearest_completed_square
#print axioms nearest_lower
#print axioms nearest_attainment
#print axioms distance_coefficient
#print axioms dual_envelope

noncomputable def root (q c : ℝ) : ℝ := (1-c)/(q-2+c)

/-- The algebraic root balances the two query types and is small enough for
the dual endpoint envelope at every q>=3. -/
theorem root_properties (q c : ℝ) (hq : 3 ≤ q) (hc : 3/4 ≤ c) (hc1 : c < 1)
    (hscale : (q+1)*c^2=q) :
    0 < root q c ∧ 4*q*root q c ≤ 1 ∧
      (q+1)*(1-(q-2)*root q c)^2=q*(1+root q c)^2 := by
  have hd : 0 < q-2+c := by linarith
  have hk : 0 ≤ q+1 := by linarith
  refine ⟨div_pos (by linarith) hd, ?_, ?_⟩
  · have h0 : 4*q ≤ (q+1)*(7/4)*(q-5/4) := by
      nlinarith [mul_nonneg (show 0 ≤ q-3 by linarith) (show 0 ≤ 28*q+13 by linarith)]
    have h1 : (q+1)*(7/4)*(q-5/4) ≤ (q+1)*(1+c)*(q-2+c) := by
      have hh := mul_le_mul_of_nonneg_left
        (mul_le_mul (show (7/4:ℝ) ≤ 1+c by linarith) (show q-5/4 ≤ q-2+c by linarith)
          (show 0 ≤ q-5/4 by linarith) (show 0 ≤ 1+c by linarith)) hk
      nlinarith
    have hrel : (q+1)*(1+c)*(1-c)=1 := by nlinarith [hscale]
    have heq : (q+1)*(1+c)*(q-2+c)*(1-c)=q-2+c := by
      calc
        _ = ((q+1)*(1+c)*(1-c))*(q-2+c) := by ring
        _ = q-2+c := by rw [hrel, one_mul]
    have hh := mul_le_mul_of_nonneg_right (le_trans h0 h1) (show 0 ≤ 1-c by linarith)
    rw [heq] at hh
    unfold root
    rw [← mul_div_assoc, div_le_one hd]
    exact hh
  · have hbalance : 1-(q-2)*root q c=c*(1+root q c) := by
      unfold root
      field_simp [ne_of_gt hd]
      ring
    rw [hbalance, mul_pow]
    calc
      _ = ((q+1)*c^2)*(1+root q c)^2 := by ring
      _ = _ := by rw [hscale]

/-- Both endpoint allocations dominate all joint-query counts in the larger
library. This is a continuum bound over the two count triangles. -/
theorem both_query_dual (q z s t : ℝ) (hq : 3 ≤ q) (hz : 0 ≤ z)
    (hsmall : 4*q*z ≤ 1) (hroot : (q+1)*(1-(q-2)*z)^2=q*(1+z)^2)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t ≤ q) :
    dual q z 0 s t ≤ q^2*(1+z)^2 ∧ dual q z 1 s t ≤ q^2*(1+z)^2 := by
  have hA0 : dual q z 0 q 0=q^2*(1+z)^2 := by unfold dual; ring
  have hB1 : dual q z 1 0 q=q^2*(1+z)^2 := by
    have hid : dual q z 1 0 q=q*(q+1)*(1-(q-2)*z)^2 := by unfold dual; ring
    rw [hid]
    nlinarith [congrArg (fun x : ℝ => q*x) hroot]
  have hA1 : dual q z 1 q 0 ≤ q^2*(1+z)^2 := by
    have hp := mul_nonneg (show 0 ≤ q by linarith)
      (show 0 ≤ (q-1)*z^2+2*q*z from add_nonneg
        (mul_nonneg (by linarith) (sq_nonneg z)) (mul_nonneg (by linarith) hz))
    have hid : q^2*(1+z)^2-dual q z 1 q 0=q*((q-1)*z^2+2*q*z) := by unfold dual; ring
    linarith
  have hB0 : dual q z 0 0 q ≤ q^2*(1+z)^2 := by
    have hp := mul_nonneg (show 0 ≤ q*(q+1)*z by positivity)
      (show 0 ≤ 2-(2*q-3)*z by nlinarith)
    have hid : dual q z 1 0 q-dual q z 0 0 q=q*(q+1)*z*(2-(2*q-3)*z) := by unfold dual; ring
    linarith
  constructor
  · exact dual_envelope q z 0 s t _ hq hz hsmall (by norm_num) (by norm_num)
      hs ht hst hA0.le hB0
  · exact dual_envelope q z 1 s t _ hq hz hsmall (by norm_num) (by norm_num)
      hs ht hst hA1 hB1.le

/-- Closed-form dual certificate for every width m=2(q+1)>=8. -/
theorem all_width_both_query_dual (q s t : ℝ) (hq : 3 ≤ q)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t ≤ q) :
    dual q (root q (scale q)) 0 s t ≤ q^2*(1+root q (scale q))^2 ∧
    dual q (root q (scale q)) 1 s t ≤ q^2*(1+root q (scale q))^2 := by
  have hc := scale_properties q hq
  have hz := root_properties q _ hq hc.1 hc.2.1 hc.2.2
  exact both_query_dual q _ s t hq hz.1.le hz.2.1 hz.2.2 hs ht hst

/-- The dual and primal certificates use exactly the same normalized value. -/
theorem dual_value_equals_primal (q : ℝ) (hq : 3 ≤ q) :
    q^2*(1+root q (scale q))^2/(q*(q+1))=value q (scale q) := by
  have hc := scale_properties q hq
  have hd : q-2+scale q ≠ 0 := by linarith [hc.1]
  have hp : q ≠ 0 := by linarith
  have hk : q+1 ≠ 0 := by linarith
  have htarget : 1+root q (scale q)=target q (scale q) := by
    unfold root target
    field_simp [hd]
    ring
  rw [htarget]
  unfold target value
  field_simp [hd, hp, hk]
  nlinarith [congrArg (fun x : ℝ => (q-1)^2*x) hc.2.2]

#print axioms root_properties
#print axioms both_query_dual
#print axioms all_width_both_query_dual
#print axioms dual_value_equals_primal

/-- The explicit mixture covers all alternative exchange distances, not only
the adjacent worlds used by the dual certificate. -/
theorem all_distances_lower (q d t : ℝ) (hq : 3 ≤ q) (hd : 1 ≤ d) (hdq : d ≤ q) :
    value q (scale q) ≤ designLoss q (scale q) d t := by
  let v := (q-d-1)*t/(q-2)
  have hc := scale_properties q hq
  have hw := parameters q _ hq hc.1 hc.2.1
  have hk : 0 < q+1 := by linarith
  have hr : 0 < q-2 := by linarith
  have hbase : q*(q-d-1)^2/(q-2)^2 ≤ d*(d*(q-1)+1) :=
    (div_le_iff₀ (sq_pos_of_pos hr)).mpr (distance_coefficient q d hq hd hdq)
  have hdiv := div_le_div_of_nonneg_right hbase hk.le
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdiv (sq_nonneg t))
    (show 0 ≤ 1-weight q (scale q) by linarith [hw.2.1])
  have hi : (q*(q-d-1)^2/(q-2)^2/(q+1))*t^2 =
      (1*(1*(q-1)+1)/(q+1))*v^2 := by
    dsimp [v]
    field_simp [ne_of_gt hr, ne_of_gt hk]
    ring
  have hb : ((q-1)-(q-1-1)*v)^2=((q-1)-(q-d-1)*t)^2 := by
    dsimp [v]
    field_simp [ne_of_gt hr]
    ring
  rw [hi] at hm
  have hn := nearest_lower q v hq
  unfold designLoss at hn ⊢
  rw [hb] at hn
  nlinarith

/-- Scalar Q measurements do not invalidate the larger-library dual. -/
theorem scalar_dual (q z : ℝ) (hq : 3 ≤ q) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (1-z)^2/(q+1) ≤ q*(1+z)^2/(q+1) ∧
    (1+(q-1)*z^2)/q ≤ q*(1+z)^2/(q+1) ∧
    z^2 ≤ q*(1+z)^2/(q+1) := by
  have hk : 0 < q+1 := by linarith
  have hp : 0 < q := by linarith
  refine ⟨(div_le_div_iff_of_pos_right hk).mpr ?_, (div_le_div_iff₀ hp hk).mpr ?_,
    (le_div_iff₀ hk).mpr ?_⟩
  · have hh := mul_nonneg (show 0 ≤ q-1 by linarith) (sq_nonneg z)
    have hh' := mul_nonneg (show 0 ≤ q+1 by linarith) hz
    nlinarith
  · have hh := mul_nonneg (sq_nonneg q) hz
    nlinarith [sq_nonneg z]
  · have hh := mul_nonneg hp.le hz
    have hsq : z^2 ≤ 1 := by nlinarith
    nlinarith

#print axioms all_distances_lower
#print axioms scalar_dual
end CIGAMF.P13.D6ExpandedAllocation
