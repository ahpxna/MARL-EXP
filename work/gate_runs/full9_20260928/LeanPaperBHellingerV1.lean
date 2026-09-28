import Mathlib

/-!
# Paper B, step B6: a moment contrast forces a Hellinger separation.

## WHY THIS MODULE EXISTS

The identification lower bound needs the two observation laws to be at least `h^r` apart in
Hellinger.  Computing that distance directly means expanding a Gaussian-mixture integral and
identifying the leading coefficient, which is delicate and easy to get wrong.

There is a cheaper route that gives the same order, and this module supplies it.  If any
bounded statistic separates the two laws in expectation, the Hellinger distance cannot be
small: by Cauchy-Schwarz,

    (E_P f - E_Q f)^2  <=  4 H^2(P, Q) * (E_P f^2 + E_Q f^2).

Applied with `f(y) = y^2` it turns the decision contrast `12h` into `H^2 >= c h^2`; applied
with `f(y) = y^(r+1)` it turns the identification contrast `2(r+1) r!/r^r h^r` into
`H^2 >= c_r h^(2r)`.  Only a NON-ZERO leading coefficient and a bounded high moment are
needed; no integral has to be evaluated exactly.

## WHAT IS PROVED

* `hellinger_lower_of_moment_contrast` -- the inequality above, on a finite outcome set,
  with the square roots carried as hypotheses so no `Real.sqrt` enters the algebra.
* `hellinger_pos_of_contrast_ne_zero` -- hence a non-zero contrast forces a strictly
  positive Hellinger distance, with the explicit constant.

## WHAT THIS DOES NOT ESTABLISH

- **Finite outcome set.**  The observation in the construction is real-valued; the same
  Cauchy-Schwarz argument runs verbatim with densities and integrals, and that version is
  not formalised here.
- The bounded-moment hypothesis `E_P f^2 + E_Q f^2 <= C` is an input.  For the construction
  it follows from the Gaussian mixture having all moments finite and uniformly bounded for
  `h` in a compact range, which is not proved here.
- This gives a LOWER bound on Hellinger from a contrast.  The matching upper bound on KL,
  which is what bounds every adaptive policy, is the separate uniform-remainder estimate and
  is not in this module.
-/

set_option maxHeartbeats 1000000

namespace CIGAMF.P13.PaperBHellinger

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The discrete Cauchy-Schwarz inequality, proved here rather than located, so the module
does not depend on a particular Mathlib spelling. -/
theorem cauchy_schwarz (a b : ι → ℝ) :
    (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) := by
  classical
  set A := ∑ i, a i ^ 2 with hA
  set B := ∑ i, b i ^ 2 with hB
  set C := ∑ i, a i * b i with hC
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases eq_or_lt_of_le hBnn with hB0 | hBpos
  · have hb : ∀ i ∈ (univ : Finset ι), b i = 0 := by
      intro i hi
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ (univ : Finset ι)) => sq_nonneg (b j))).mp hB0.symm i hi
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
    have hCz : C = 0 := by
      rw [hC]
      exact Finset.sum_eq_zero fun i hi => by rw [hb i hi]; ring
    rw [hCz, ← hB0]
    simp
  · have hnn : ∀ t : ℝ, 0 ≤ A + 2 * t * C + t ^ 2 * B := by
      intro t
      have hexp : A + 2 * t * C + t ^ 2 * B = ∑ i, (a i + t * b i) ^ 2 := by
        rw [hA, hB, hC, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hexp]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have h := hnn (-C / B)
    have hrw : A + 2 * (-C / B) * C + (-C / B) ^ 2 * B = A - C ^ 2 / B := by
      field_simp
      ring
    rw [hrw] at h
    have hle : C ^ 2 / B ≤ A := by linarith
    exact (div_le_iff₀ hBpos).mp hle

/-- **A moment contrast forces a Hellinger separation.**

`sp` and `sq` are the pointwise square roots of the two laws, carried as hypotheses so the
argument stays polynomial.  `H2` is the squared Hellinger distance, `2 H2 = sum (sp - sq)^2`.
-/
theorem hellinger_lower_of_moment_contrast
    (p q sp sq f : ι → ℝ) (H2 : ℝ)
    (hp : ∀ i, sp i ^ 2 = p i) (hq : ∀ i, sq i ^ 2 = q i)
    (hH : 2 * H2 = ∑ i, (sp i - sq i) ^ 2) :
    ((∑ i, f i * p i) - (∑ i, f i * q i)) ^ 2
      ≤ 4 * H2 * ((∑ i, f i ^ 2 * p i) + (∑ i, f i ^ 2 * q i)) := by
  classical
  -- the contrast is a pairing of (sp - sq) against f (sp + sq)
  have hpair : (∑ i, f i * p i) - (∑ i, f i * q i)
      = ∑ i, (sp i - sq i) * (f i * (sp i + sq i)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hp i, ← hq i]
    ring
  -- Cauchy-Schwarz
  have hcs : (∑ i, (sp i - sq i) * (f i * (sp i + sq i))) ^ 2
      ≤ (∑ i, (sp i - sq i) ^ 2) * (∑ i, (f i * (sp i + sq i)) ^ 2) :=
    cauchy_schwarz _ _
  -- the second factor is controlled by the two second moments
  have hsq : ∀ i, (f i * (sp i + sq i)) ^ 2 ≤ 2 * (f i ^ 2 * p i + f i ^ 2 * q i) := by
    intro i
    have hexp : (f i * (sp i + sq i)) ^ 2
        = f i ^ 2 * (sp i ^ 2 + 2 * (sp i * sq i) + sq i ^ 2) := by ring
    have hab : 2 * (sp i * sq i) ≤ sp i ^ 2 + sq i ^ 2 := by nlinarith [sq_nonneg (sp i - sq i)]
    have hf : (0 : ℝ) ≤ f i ^ 2 := sq_nonneg _
    rw [hexp, ← hp i, ← hq i]
    nlinarith [hab, hf]
  have hsum2 : (∑ i, (f i * (sp i + sq i)) ^ 2)
      ≤ 2 * ((∑ i, f i ^ 2 * p i) + (∑ i, f i ^ 2 * q i)) := by
    have := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset ι)) => hsq i
    calc (∑ i, (f i * (sp i + sq i)) ^ 2)
        ≤ ∑ i, 2 * (f i ^ 2 * p i + f i ^ 2 * q i) := this
      _ = 2 * ((∑ i, f i ^ 2 * p i) + (∑ i, f i ^ 2 * q i)) := by
          rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  -- assemble
  have hH2nn : 0 ≤ 2 * H2 := by
    rw [hH]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [hpair]
  calc (∑ i, (sp i - sq i) * (f i * (sp i + sq i))) ^ 2
      ≤ (∑ i, (sp i - sq i) ^ 2) * (∑ i, (f i * (sp i + sq i)) ^ 2) := hcs
    _ = (2 * H2) * (∑ i, (f i * (sp i + sq i)) ^ 2) := by rw [hH]
    _ ≤ (2 * H2) * (2 * ((∑ i, f i ^ 2 * p i) + (∑ i, f i ^ 2 * q i))) :=
        mul_le_mul_of_nonneg_left hsum2 hH2nn
    _ = 4 * H2 * ((∑ i, f i ^ 2 * p i) + (∑ i, f i ^ 2 * q i)) := by ring

/-- **A non-zero contrast forces a strictly positive Hellinger distance**, with an explicit
constant, and without evaluating any integral.

WHICH DIRECTION THIS GIVES.  A LOWER bound on `H^2` says the two worlds are FAR apart, so it
bounds the cost of telling them apart from ABOVE: a test exists that succeeds at that rate.
It does NOT say every algorithm needs many samples.

To lower-bound the sample cost one needs the opposite inequality -- an UPPER bound on the
information a single query can carry, uniformly over the permitted query class -- and then a
transcript or testing argument on top of it.  `LeanPaperBTranscriptKLV1` has the chain rule
for that route, for finite observations and deterministic policies; the continuous
randomised case is open.  Until it closes, the identification LOWER bound is established
only on the finite query panel that was checked, not for every query. -/
theorem hellinger_pos_of_contrast_ne_zero
    (p q sp sq f : ι → ℝ) (H2 C : ℝ)
    (hp : ∀ i, sp i ^ 2 = p i) (hq : ∀ i, sq i ^ 2 = q i)
    (hH : 2 * H2 = ∑ i, (sp i - sq i) ^ 2)
    (hC : (∑ i, f i ^ 2 * p i) + (∑ i, f i ^ 2 * q i) ≤ C) (hCpos : 0 < C)
    (delta : ℝ) (hdelta : |(∑ i, f i * p i) - (∑ i, f i * q i)| = delta) :
    delta ^ 2 / (4 * C) ≤ H2 := by
  have hmain := hellinger_lower_of_moment_contrast p q sp sq f H2 hp hq hH
  have hsq : delta ^ 2 = ((∑ i, f i * p i) - (∑ i, f i * q i)) ^ 2 := by
    rw [← hdelta, sq_abs]
  have hH2nn : 0 ≤ H2 := by
    have : 0 ≤ 2 * H2 := by
      rw [hH]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  have hstep : delta ^ 2 ≤ 4 * H2 * C := by
    rw [hsq]
    refine le_trans hmain ?_
    exact mul_le_mul_of_nonneg_left hC (by linarith)
  rw [div_le_iff₀ (by linarith)]
  linarith

#print axioms cauchy_schwarz
#print axioms hellinger_lower_of_moment_contrast
#print axioms hellinger_pos_of_contrast_ne_zero

end CIGAMF.P13.PaperBHellinger
