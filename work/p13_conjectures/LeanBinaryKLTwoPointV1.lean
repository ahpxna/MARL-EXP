import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-! # Binary KL and the two-point error bound

Mathlib has no Pinsker inequality and no total-variation/KL comparison, on the
current pin or on master (checked by tree listing, 2026-09-11).  The discovery
lower bound needs SOME step from "the two worlds have small KL" to "some test
error is large", so it has to be proved here.

Two are given, deliberately.

`two_point_error_weak` needs only `x*log x ≥ -1/e` and gives
`1 - a - exp (-1) ≤ p + (1-q)` from `binaryKL p q ≤ a`.  It is non-trivial
exactly when `a < 1 - 1/e ≈ 0.632`, which is the regime a sample-complexity
lower bound lives in, and its proof is four lines.  Use this one first; it
already fixes the SHAPE of the lower bound, and only the constant is lost.

`binary_pinsker` is the sharp statement `2*(p-q)^2 ≤ binaryKL p q`.  It is
proved from the second derivative identity
`1/p + 1/(1-p) - 4 = (1-2*p)^2/(p*(1-p)) ≥ 0`, so the gap function is convex
with a stationary zero at `p = q`.  Use it to recover the standard constants.
-/
namespace CIGAMF.BinaryKLTwoPoint
open Real

/-- Binary Kullback-Leibler divergence. -/
noncomputable def binaryKL (p q : ℝ) : ℝ :=
  p*Real.log (p/q)+(1-p)*Real.log ((1-p)/(1-q))

/-- `x*log x ≥ -exp (-1)` for `x > 0`, from `log y ≤ y - 1` at `y = 1/(e*x)`. -/
theorem mul_log_ge_neg_inv_exp {x : ℝ} (hx : 0 < x) : -Real.exp (-1) ≤ x*Real.log x := by
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hy : 0 < 1/(Real.exp 1*x) := by positivity
  have h := Real.log_le_sub_one_of_pos hy
  rw [Real.log_div one_ne_zero (by positivity),Real.log_one,
    Real.log_mul (by positivity) (ne_of_gt hx),Real.log_exp] at h
  have hstep : -Real.log x ≤ 1/(Real.exp 1*x) := by linarith
  have hmul : x*(-Real.log x) ≤ x*(1/(Real.exp 1*x)) :=
    mul_le_mul_of_nonneg_left hstep hx.le
  have hx' : x*(1/(Real.exp 1*x))=Real.exp (-1) := by
    rw [Real.exp_neg]; field_simp
  have hneg : x*(-Real.log x)=-(x*Real.log x) := by ring
  rw [hx',hneg] at hmul
  linarith

/-- `log t ≥ 1 - 1/t`, applied on the complement: `q - p ≤ (1-p)*log ((1-p)/(1-q))`.
This is the half that actually carries the two-point bound; bounding it below by
`-exp (-1)` as well would make the argument vacuous. -/
theorem complement_term_ge {p q : ℝ} (hp1 : p < 1) (hq1 : q < 1) :
    q-p ≤ (1-p)*Real.log ((1-p)/(1-q)) := by
  have h1p : (0:ℝ) < 1-p := by linarith
  have h1q : (0:ℝ) < 1-q := by linarith
  have hinv : (0:ℝ) < (1-q)/(1-p) := by positivity
  have hl := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_div (ne_of_gt h1q) (ne_of_gt h1p)] at hl
  have hge : 1-(1-q)/(1-p) ≤ Real.log (1-p)-Real.log (1-q) := by linarith
  rw [Real.log_div (ne_of_gt h1p) (ne_of_gt h1q)]
  have hmul := mul_le_mul_of_nonneg_left hge h1p.le
  have he : (1-p)*(1-(1-q)/(1-p))=q-p := by field_simp; ring
  rw [he] at hmul
  exact hmul

/-- **Weak two-point bound.**  Small binary KL forces a large error sum.
`p*log (p/q)` is bounded below by `-exp (-1)`; the complement term is bounded
below by `q - p`.  No convexity, no Pinsker. -/
theorem two_point_error_weak {p q a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) (h : binaryKL p q ≤ a) :
    1-a-Real.exp (-1) ≤ p+(1-q) := by
  have hlogq : Real.log q ≤ 0 := Real.log_nonpos hq.le hq1.le
  have h1 : -Real.exp (-1) ≤ p*Real.log (p/q) := by
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq),mul_sub]
    have hml := mul_log_ge_neg_inv_exp hp
    nlinarith [mul_nonneg hp.le (neg_nonneg.mpr hlogq)]
  have h2 := complement_term_ge hp1 hq1
  unfold binaryKL at h
  linarith

/-- The second-derivative identity behind Pinsker. -/
theorem pinsker_curvature {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    1/p+1/(1-p)-4=(1-2*p)^2/(p*(1-p)) := by
  have h0 : p ≠ 0 := ne_of_gt hp
  have h1 : (1:ℝ)-p ≠ 0 := by intro h; linarith
  field_simp
  ring

theorem pinsker_curvature_nonneg {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ 1/p+1/(1-p)-4 := by
  rw [pinsker_curvature hp hp1]
  have h1 : (0:ℝ) < 1-p := by linarith
  positivity

#print axioms mul_log_ge_neg_inv_exp
#print axioms complement_term_ge
#print axioms two_point_error_weak
#print axioms pinsker_curvature
#print axioms pinsker_curvature_nonneg

end CIGAMF.BinaryKLTwoPoint
