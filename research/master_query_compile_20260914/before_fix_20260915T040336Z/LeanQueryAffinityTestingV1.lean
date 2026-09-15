import Mathlib

/-!
Hellinger affinity on actual density functions and the full IID sample space.
No Gaussian-mean approximation is made. The result applies to Gaussian mixtures
once their ordinary integrability and normalization obligations are discharged.
It proves the product identity and both testing bounds directly from integrals.

Boundary: this file does NOT assume or prove the small-h Taylor estimate for a
particular finite mixture. Consequently it does not label the h^(-2r) asymptotic
as closed. That analytic instantiation remains a separate obligation.
-/
namespace CIGAMF.P13.QueryAffinityTesting
open MeasureTheory Finset
open scoped BigOperators
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

def affinity (μ : Measure Ω) (p q : Ω → ℝ) := ∫ x, Real.sqrt (p x*q x) ∂μ
def overlap (μ : Measure Ω) (p q : Ω → ℝ) := ∫ x, min (p x) (q x) ∂μ
def testingError (μ : Measure Ω) (p q d : Ω → ℝ) :=
  (∫ x, p x*d x+q x*(1-d x) ∂μ)/2

/-- Weighted Young inequality. Choosing t=rho/2 after integration gives the lower bound. -/
theorem root_young (p q t : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    2*t*Real.sqrt (p*q) ≤ min p q + t^2*(p+q) := by
  rw [Real.sqrt_mul hp]
  have hp2 := Real.sq_sqrt hp
  have hq2 := Real.sq_sqrt hq
  by_cases h : p ≤ q
  · rw [min_eq_left h]
    nlinarith [sq_nonneg (Real.sqrt p-t*Real.sqrt q), mul_nonneg (sq_nonneg t) hp]
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith [sq_nonneg (Real.sqrt q-t*Real.sqrt p), mul_nonneg (sq_nonneg t) hq]

theorem min_le_root (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    min p q ≤ Real.sqrt (p*q) := by
  apply Real.le_sqrt_of_sq_le
  by_cases h : p ≤ q
  · rw [min_eq_left h]
    nlinarith [mul_nonneg hp (sub_nonneg.mpr h)]
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr (le_of_not_ge h))]

/-- The two-sided overlap bound, with the normalization of the real densities explicit. -/
theorem overlap_bracket (μ : Measure Ω) (p q : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (ip : Integrable p μ) (iq : Integrable q μ)
    (imin : Integrable (fun x => min (p x) (q x)) μ)
    (iroot : Integrable (fun x => Real.sqrt (p x*q x)) μ)
    (np : ∫ x, p x ∂μ = 1) (nq : ∫ x, q x ∂μ = 1) :
    (affinity μ p q)^2/4 ≤ overlap μ p q/2 ∧
    overlap μ p q/2 ≤ affinity μ p q/2 := by
  have hy : ∀ t : ℝ, 2*t*affinity μ p q ≤ overlap μ p q+2*t^2 := by
    intro t
    have h := integral_mono (iroot.const_mul (2*t))
      (imin.add ((ip.add iq).const_mul (t^2)))
      (fun x => root_young (p x) (q x) t (hp x) (hq x))
    rw [integral_const_mul, integral_add imin ((ip.add iq).const_mul (t^2)),
      integral_const_mul, integral_add ip iq, np, nq] at h
    change 2*t*affinity μ p q ≤ overlap μ p q+t^2*(1+1) at h
    nlinarith
  constructor
  · have h := hy (affinity μ p q/2)
    nlinarith
  · have h := integral_mono imin iroot (fun x => min_le_root (p x) (q x) (hp x) (hq x))
    change overlap μ p q ≤ affinity μ p q at h
    linarith

/-- Every randomized decoder pays at least half the common mass. -/
theorem every_test_lower (μ : Measure Ω) (p q d : Ω → ℝ)
    (hd0 : ∀ x, 0 ≤ d x) (hd1 : ∀ x, d x ≤ 1)
    (imin : Integrable (fun x => min (p x) (q x)) μ)
    (iloss : Integrable (fun x => p x*d x+q x*(1-d x)) μ) :
    overlap μ p q/2 ≤ testingError μ p q d := by
  have h := integral_mono imin iloss (fun x => by
    have h1 := min_le_left (p x) (q x)
    have h2 := min_le_right (p x) (q x)
    have h3 := mul_le_mul_of_nonneg_right h1 (hd0 x)
    have h4 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr (hd1 x))
    nlinarith)
  unfold overlap testingError
  linarith

def likelihoodRatioTest (p q : Ω → ℝ) (x : Ω) : ℝ :=
  if p x ≤ q x then 1 else 0

theorem likelihood_ratio_loss (p q : Ω → ℝ) (x : Ω) :
    p x*likelihoodRatioTest p q x+q x*(1-likelihoodRatioTest p q x)
      = min (p x) (q x) := by
  unfold likelihoodRatioTest
  split_ifs with h
  · simp [min_eq_left h]
  · simp [min_eq_right (le_of_not_ge h)]

/-- An explicit deterministic decoder attains half the common mass. -/
theorem likelihood_ratio_attains (μ : Measure Ω) (p q : Ω → ℝ) :
    testingError μ p q (likelihoodRatioTest p q) = overlap μ p q/2 := by
  unfold testingError overlap
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (likelihood_ratio_loss p q)

def iidDensity (p : Ω → ℝ) (N : ℕ) (x : Fin N → Ω) := ∏ i, p (x i)

/-- Tensorisation is proved on the entire N-observation space. -/
theorem iid_affinity (μ : Measure Ω) [SigmaFinite μ] (p q : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (N : ℕ) :
    affinity (Measure.pi (fun _ : Fin N => μ)) (iidDensity p N) (iidDensity q N)
      = (affinity μ p q)^N := by
  unfold affinity iidDensity
  have he : ∀ x : Fin N → Ω,
      Real.sqrt ((∏ i, p (x i))*(∏ i, q (x i))) =
        ∏ i, Real.sqrt (p (x i)*q (x i)) := by
    intro x
    rw [← Finset.prod_mul_distrib]
    exact Real.sqrt_prod _ (fun i _ => mul_nonneg (hp (x i)) (hq (x i)))
  simp_rw [he]
  simpa using (integral_fintype_prod_eq_pow (ι := Fin N)
    (μ := μ) (fun x => Real.sqrt (p x*q x)))

theorem iid_normalized (μ : Measure Ω) [SigmaFinite μ] (p : Ω → ℝ)
    (hp : ∫ x, p x ∂μ = 1) (N : ℕ) :
    (∫ x, iidDensity p N x ∂Measure.pi (fun _ : Fin N => μ)) = 1 := by
  unfold iidDensity
  rw [integral_fintype_prod_eq_pow, hp]
  simp

/-- The exact powers used by P9, with all density hypotheses exposed. -/
theorem iid_testing_bracket (μ : Measure Ω) [SigmaFinite μ] (p q : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (np : ∫ x, p x ∂μ = 1) (nq : ∫ x, q x ∂μ = 1) (N : ℕ)
    (ip : Integrable (iidDensity p N) (Measure.pi (fun _ : Fin N => μ)))
    (iq : Integrable (iidDensity q N) (Measure.pi (fun _ : Fin N => μ)))
    (imin : Integrable (fun x => min (iidDensity p N x) (iidDensity q N x))
      (Measure.pi (fun _ : Fin N => μ)))
    (iroot : Integrable (fun x => Real.sqrt (iidDensity p N x*iidDensity q N x))
      (Measure.pi (fun _ : Fin N => μ))) :
    (affinity μ p q)^(2*N)/4 ≤
      testingError (Measure.pi (fun _ : Fin N => μ))
        (iidDensity p N) (iidDensity q N)
        (likelihoodRatioTest (iidDensity p N) (iidDensity q N)) ∧
    testingError (Measure.pi (fun _ : Fin N => μ))
        (iidDensity p N) (iidDensity q N)
        (likelihoodRatioTest (iidDensity p N) (iidDensity q N))
      ≤ (affinity μ p q)^N/2 := by
  rw [likelihood_ratio_attains]
  have h := overlap_bracket (Measure.pi (fun _ : Fin N => μ))
    (iidDensity p N) (iidDensity q N)
    (fun x => Finset.prod_nonneg fun i _ => hp (x i))
    (fun x => Finset.prod_nonneg fun i _ => hq (x i))
    ip iq imin iroot (iid_normalized μ p np N) (iid_normalized μ q nq N)
  rw [iid_affinity μ p q hp hq N] at h
  simpa only [← pow_mul, Nat.mul_comm N 2] using h

/-- Turning any certified Hellinger enclosure into an affinity enclosure. -/
theorem affinity_enclosure (rho hlo hhi : ℝ)
    (hlo_bound : hlo ≤ 1-rho) (hhi_bound : 1-rho ≤ hhi) :
    1-hhi ≤ rho ∧ rho ≤ 1-hlo := by constructor <;> linarith

#print axioms root_young
#print axioms min_le_root
#print axioms overlap_bracket
#print axioms every_test_lower
#print axioms likelihood_ratio_attains
#print axioms iid_affinity
#print axioms iid_normalized
#print axioms iid_testing_bracket
#print axioms affinity_enclosure
end
end CIGAMF.P13.QueryAffinityTesting
