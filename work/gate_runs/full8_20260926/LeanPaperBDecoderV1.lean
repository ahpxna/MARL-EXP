import «LeanPaperBSafeOrderV1»

/-!
# Paper B: the safe decoder, with the uniformity a class test actually needs

An upper bound needs a decoder, not a collection of pairwise error bounds.  Two things have
to be got right, and the second is the one that is easy to skip.

**A test between two CLASSES is not a test between two representatives.**  What has to hold
is

    sup over theta in C   Pr_theta(the test says D)  <=  delta',
    sup over lambda in D  Pr_lambda(the test says C) <=  delta',

uniformly over each class.  Picking one world from each class and testing those two says
nothing about the others.  The lemma below is the uniform version: if a bounded statistic's
mean sits within `R` of a class value for EVERY world of that class, and the two class
values are separated by more than `2R + 2 tol`, then ONE threshold at the midpoint
classifies every world of either class correctly whenever the empirical mean is within
`tol` of its own world's mean.  The per-world concentration is the only probabilistic input,
and the class uniformity comes from `R`, not from a representative.

**The output has to exist.**  After elimination the surviving candidate set lies inside the
true world's class at order `s_safe`; `SafeAt` is exactly the statement that such a set has
a common safe answer, so the decoder has something to return.  That is why the decoder is
built on the law of `LeanPaperBSafeOrderV1` rather than beside it.

WHAT IS NOT HERE.  The concentration itself (a bounded statistic and Hoeffding), the queries
realising the separation at each order, and the TOTAL sample budget across the tests --- the
number of distinct queries and the number of tests are not the same quantity, and neither is
the per-test sample count.  Those are the remaining half of B6.
-/

namespace CIGAMF.P13.PaperBDecoder

open Finset
open CIGAMF.P13.PaperBSafe

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]

/-! ## The composite test -/

/-- **One threshold separates two classes, uniformly over both.**  `m θ` is the statistic's
mean at world `θ`; `R` bounds how far that can sit from the class value; `tol` bounds the
empirical deviation.  No representative is chosen. -/
theorem composite_test_low (m : W → ℝ) (C : Finset W) (muC muD R tol : ℝ)
    (hC : ∀ θ ∈ C, |m θ - muC| ≤ R)
    (hsep : muC + 2 * R + 2 * tol < muD)
    (θ : W) (hθ : θ ∈ C) (x : ℝ) (hx : |x - m θ| ≤ tol) :
    x < (muC + muD) / 2 := by
  have h1 := abs_le.mp (hC θ hθ)
  have h2 := abs_le.mp hx
  linarith [h1.2, h2.2]

theorem composite_test_high (m : W → ℝ) (D : Finset W) (muC muD R tol : ℝ)
    (hD : ∀ lam ∈ D, |m lam - muD| ≤ R)
    (hsep : muC + 2 * R + 2 * tol < muD)
    (lam : W) (hlam : lam ∈ D) (x : ℝ) (hx : |x - m lam| ≤ tol) :
    (muC + muD) / 2 < x := by
  have h1 := abs_le.mp (hD lam hlam)
  have h2 := abs_le.mp hx
  linarith [h1.1, h2.1]

/-- **The test is decisive**: on the good event the threshold puts every world of `C` on one
side and every world of `D` on the other, so the classification is a function of the data
and not of which representative was picked. -/
theorem composite_test_separates (m : W → ℝ) (C D : Finset W) (muC muD R tol : ℝ)
    (hC : ∀ θ ∈ C, |m θ - muC| ≤ R) (hD : ∀ lam ∈ D, |m lam - muD| ≤ R)
    (hsep : muC + 2 * R + 2 * tol < muD)
    (θ : W) (hθ : θ ∈ C) (lam : W) (hlam : lam ∈ D)
    (x y : ℝ) (hx : |x - m θ| ≤ tol) (hy : |y - m lam| ≤ tol) :
    x < (muC + muD) / 2 ∧ (muC + muD) / 2 < y :=
  ⟨composite_test_low m C muC muD R tol hC hsep θ hθ x hx,
   composite_test_high m D muC muD R tol hD hsep lam hlam y hy⟩

/-- The separation the test needs is implied by a gap that beats the class radius and the
tolerance --- stated so the sample size enters in one place. -/
theorem separation_of_gap (muC muD R tol gap : ℝ)
    (hgap : muD - muC = gap) (h : 2 * R + 2 * tol < gap) :
    muC + 2 * R + 2 * tol < muD := by linarith

/-! ## Elimination, and why the output exists -/

/-- The surviving candidate set: worlds not eliminated by any test. -/
def survivors (elim : W → Prop) [DecidablePred elim] : Finset W :=
  Finset.univ.filter (fun w => ¬ elim w)

theorem truth_mem_survivors (elim : W → Prop) [DecidablePred elim] (θ : W)
    (hθ : ¬ elim θ) : θ ∈ survivors elim := by
  simp [survivors, hθ]

/-- **The decoder has something to return.**  If the survivors are still together at level
`s` and order `s` suffices for safe decisions, then they share a safe answer --- and the
truth is among them, so the answer is safe at the truth in particular. -/
theorem decoder_output_exists (sep : W → W → ℕ) (safe : W → Finset A) (s : ℕ)
    (hsafe : SafeAt sep safe s) (H : Finset W) (htog : Together sep s H) :
    ∃ a : A, ∀ θ ∈ H, a ∈ safe θ := by
  have h := hsafe H htog
  unfold Unsafe at h
  push_neg at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun θ hθ => ha θ hθ⟩

/-- **And it is safe at the true world.**  The step the pairwise-error accounting does not
give: correctness of the OUTPUT, not of the tests. -/
theorem decoder_is_safe_at_truth (sep : W → W → ℕ) (safe : W → Finset A) (s : ℕ)
    (hsafe : SafeAt sep safe s) (H : Finset W) (htog : Together sep s H)
    (θ : W) (hθ : θ ∈ H) :
    ∃ a : A, a ∈ safe θ ∧ ∀ lam ∈ H, a ∈ safe lam := by
  obtain ⟨a, ha⟩ := decoder_output_exists sep safe s hsafe H htog
  exact ⟨a, ha θ hθ, ha⟩

/-! ## Audit -/

#print axioms composite_test_low
#print axioms composite_test_high
#print axioms composite_test_separates
#print axioms separation_of_gap
#print axioms decoder_output_exists
#print axioms decoder_is_safe_at_truth

end CIGAMF.P13.PaperBDecoder
