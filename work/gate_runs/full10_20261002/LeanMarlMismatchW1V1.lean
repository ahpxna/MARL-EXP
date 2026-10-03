import Mathlib

/-!
# The mismatch law's bound: a Lipschitz age response moves by at most L · W1 (ages on a line)

Ledger L-249 / L-258 (02/10/2026): for learned receivers, the gain difference between a receiver trained on channel A and
one trained on channel B is, on two panels, linear in the difference of the Wasserstein-1 distances between the
deployment age histogram and each training age histogram (W1 on the line = the L1 distance between the cumulative
histograms).  This file proves the elementary bound behind that coordinate, for distributions on the ages 0, …, n:

  if the per-copy response `g` changes by at most `L` between consecutive ages, then
  | Σ_a (p a − q a) g a |  ≤  L · Σ_{a < n} | F_p a − F_q a |,      F_p a = Σ_{b ≤ a} p b,

whenever `p` and `q` have the same total mass (the discrete Kantorovich–Rubinstein bound on ℕ, via Abel summation), and
that W1 to a fixed deployment histogram is convex in the training histogram (so a mixture-trained receiver's mismatch is
at most the weighted mismatch of its components).

## WHAT IS PROVED
* `abel_identity` — Σ_{a ≤ n} d a · g a = Σ_{a < n} D a · (g a − g (a+1)) + D n · g n, D a = Σ_{b ≤ a} d b.
* `lipschitz_w1_bound` — the inequality above (any real p, q with equal mass; no sign or normalisation needed).
* `w1_mix_le` — W1(λ p + (1 − λ) p', q) ≤ λ W1(p, q) + (1 − λ) W1(p', q) for λ ∈ [0, 1].
* `w1_bound_tight` — equality for p = δ₀, q = δ₁, g a = L a (so the bound is attained and the hypotheses are satisfiable).

## WHAT THIS DOES NOT ESTABLISH
- That a learned receiver's value IS an expectation of a Lipschitz function of the copy-age histogram: that is a modelling
  assumption (the receiver's response to copy age, H-C / L-237, is measured, not proved Lipschitz), and the joint state
  matters beyond the age marginal.  The measured linear law (L-249, L-258) is empirical.
- Anything about which training histogram is optimal; the mixture lemma only bounds the mismatch.
-/

namespace CIGAMF.P13.MarlMismatchW1V1

open Finset

/-- Cumulative sum D a = Σ_{b ≤ a} d b. -/
def cum (d : ℕ → ℝ) (a : ℕ) : ℝ := ∑ b ∈ range (a + 1), d b

/-- W1 on the ages 0..n between p and q: Σ_{a < n} |F_p a − F_q a|. -/
def w1 (n : ℕ) (p q : ℕ → ℝ) : ℝ := ∑ a ∈ range n, |cum p a - cum q a|

theorem cum_succ (d : ℕ → ℝ) (a : ℕ) : cum d (a + 1) = cum d a + d (a + 1) := by
  unfold cum; rw [sum_range_succ]

theorem abel_identity (d g : ℕ → ℝ) (n : ℕ) :
    ∑ a ∈ range (n + 1), d a * g a = ∑ a ∈ range n, cum d a * (g a - g (a + 1)) + cum d n * g n := by
  induction n with
  | zero => simp [cum]
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ, cum_succ]
    ring

theorem cum_sub (p q : ℕ → ℝ) (a : ℕ) : cum (fun b => p b - q b) a = cum p a - cum q a := by
  unfold cum; rw [sum_sub_distrib]

theorem lipschitz_w1_bound (p q g : ℕ → ℝ) (n : ℕ) (L : ℝ)
    (hg : ∀ a, a < n → |g a - g (a + 1)| ≤ L)
    (hmass : ∑ a ∈ range (n + 1), p a = ∑ a ∈ range (n + 1), q a) :
    |∑ a ∈ range (n + 1), (p a - q a) * g a| ≤ L * w1 n p q := by
  have hD : cum (fun b => p b - q b) n = 0 := by
    rw [cum_sub]; unfold cum; rw [hmass]; ring
  rw [abel_identity (fun b => p b - q b) g n, hD, zero_mul, add_zero]
  unfold w1; rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a ha => ?_)
  rw [abs_mul, cum_sub, mul_comm L]
  exact mul_le_mul_of_nonneg_left (hg a (mem_range.mp ha)) (abs_nonneg _)

theorem cum_mix (lam : ℝ) (p p' : ℕ → ℝ) (a : ℕ) :
    cum (fun b => lam * p b + (1 - lam) * p' b) a = lam * cum p a + (1 - lam) * cum p' a := by
  unfold cum; rw [sum_add_distrib, ← mul_sum, ← mul_sum]

theorem w1_mix_le (n : ℕ) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (p p' q : ℕ → ℝ) :
    w1 n (fun b => lam * p b + (1 - lam) * p' b) q ≤ lam * w1 n p q + (1 - lam) * w1 n p' q := by
  unfold w1; rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun a _ => ?_
  rw [cum_mix]
  have e : lam * cum p a + (1 - lam) * cum p' a - cum q a
      = lam * (cum p a - cum q a) + (1 - lam) * (cum p' a - cum q a) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - lam)]

/-- Tightness (and satisfiable hypotheses): p = δ₀, q = δ₁ on the ages {0, 1}, g a = L a. -/
theorem w1_bound_tight (L : ℝ) (hL : 0 ≤ L) :
    let p : ℕ → ℝ := fun a => if a = 0 then 1 else 0
    let q : ℕ → ℝ := fun a => if a = 1 then 1 else 0
    (∀ a, a < 1 → |(fun a : ℕ => L * a) a - (fun a : ℕ => L * a) (a + 1)| ≤ L) ∧
    (∑ a ∈ range 2, p a = ∑ a ∈ range 2, q a) ∧
    |∑ a ∈ range 2, (p a - q a) * (L * a)| = L * w1 1 p q := by
  intro p q
  refine ⟨fun a _ => ?_, ?_, ?_⟩
  · push_cast; rw [show L * a - L * (a + 1) = -L by ring, abs_neg, abs_of_nonneg hL]
  · simp [p, q]
  · simp [p, q, w1, cum, sum_range_succ, abs_of_nonneg hL]

end CIGAMF.P13.MarlMismatchW1V1

#print axioms CIGAMF.P13.MarlMismatchW1V1.abel_identity
#print axioms CIGAMF.P13.MarlMismatchW1V1.lipschitz_w1_bound
#print axioms CIGAMF.P13.MarlMismatchW1V1.w1_mix_le
#print axioms CIGAMF.P13.MarlMismatchW1V1.w1_bound_tight
