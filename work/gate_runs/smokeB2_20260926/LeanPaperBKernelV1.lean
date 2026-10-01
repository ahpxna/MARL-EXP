import Mathlib

/-!
# Paper B: the adaptive transcript, on actual kernels

`LeanPaperBChangeV1` proves the horizon bound from `hdens` and a per-step `klIncr` bound, both
taken as hypotheses, over a FINITE alphabet.  That cannot support a claim quantified over
randomised adaptive policies with continuous observations.  This module supplies the two
pieces that replace it, with `Q` (queries) and `Y` (observations) arbitrary measurable spaces
-- nothing finite, nothing deterministic.

* `policy_contributes_nothing` -- composing both worlds with the SAME policy kernel adds
  exactly zero divergence.  This is the precise content of "the policy kernels cancel in the
  likelihood ratio", and it is why the resulting bound is uniform over policies rather than
  policy-dependent.  It is Mathlib's `klDiv_compProd_left`, stated at the policy.
* `round_kl_eq` -- one round of the protocol: draw the query from the shared policy, then
  observe under the world's own kernel.  The round's divergence is the history's divergence
  plus the round's CONDITIONAL observation divergence, with no policy term.  This is Mathlib's
  chain rule composed with the cancellation, and it is the step the induction needs.
* `kl_le_of_rounds` -- the induction: `n` rounds cost at most `n` times the per-round
  conditional divergence, whatever the policy is.

The abstract form is deliberate.  An earlier attempt built the history as a recursive type;
the recursion's `MeasurableSpace` instance does not reduce definitionally, so the statements
became about a type Lean could not identify with the composition it was supposed to be.
Stating the round and the induction separately keeps each one about the object it is actually
about, and a concrete protocol composes them.

**What is still owed, stated plainly.**  `kl_le_of_rounds` takes the per-round CONDITIONAL
divergence bound as an input.  Reducing that to a per-query supremum
`sup_q KL(P_θ^q, P_λ^q) ≤ C` needs the integral form of the conditional divergence, which
Mathlib does not have -- its `ChainRule.lean` lists it as a TODO.  So this turns four
obligations into one, and names the one.  It does not close #7.
-/

namespace CIGAMF.P13.PaperBKernel

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

/-! ## The policy cancels -/

/-- **A shared policy contributes no divergence.** -/
theorem policy_contributes_nothing {α Q : Type*} [MeasurableSpace α] [MeasurableSpace Q]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (policy : Kernel α Q) [IsMarkovKernel policy] :
    klDiv (μ ⊗ₘ policy) (ν ⊗ₘ policy) = klDiv μ ν :=
  klDiv_compProd_left μ ν policy

/-! ## One round -/

/-- **One round of an adaptive protocol.**  `μP`, `μQ` are the two worlds' history laws;
`policy` is the same measurable function of the history under both; `obsP`, `obsQ` are the
worlds' observation kernels.  The round's divergence splits into the history's and the
round's conditional observation term -- and the policy contributes nothing, so the split is
uniform over policies. -/
theorem round_kl_eq {α Q Y : Type*} [MeasurableSpace α] [MeasurableSpace Q]
    [MeasurableSpace Y] (μP μQ : Measure α) [IsFiniteMeasure μP] [IsFiniteMeasure μQ]
    (policy : Kernel α Q) [IsMarkovKernel policy]
    (obsP obsQ : Kernel (α × Q) Y) [IsMarkovKernel obsP] [IsMarkovKernel obsQ] :
    klDiv ((μP ⊗ₘ policy) ⊗ₘ obsP) ((μQ ⊗ₘ policy) ⊗ₘ obsQ)
      = klDiv μP μQ
        + klDiv ((μP ⊗ₘ policy) ⊗ₘ obsP) ((μP ⊗ₘ policy) ⊗ₘ obsQ) := by
  rw [klDiv_compProd_eq_add (μP ⊗ₘ policy) (μQ ⊗ₘ policy) obsP obsQ,
    policy_contributes_nothing μP μQ policy]

/-- **A round costs at most the round's conditional divergence.** -/
theorem round_kl_le {α Q Y : Type*} [MeasurableSpace α] [MeasurableSpace Q]
    [MeasurableSpace Y] (μP μQ : Measure α) [IsFiniteMeasure μP] [IsFiniteMeasure μQ]
    (policy : Kernel α Q) [IsMarkovKernel policy]
    (obsP obsQ : Kernel (α × Q) Y) [IsMarkovKernel obsP] [IsMarkovKernel obsQ]
    (C : ℝ≥0∞)
    (hcond : klDiv ((μP ⊗ₘ policy) ⊗ₘ obsP) ((μP ⊗ₘ policy) ⊗ₘ obsQ) ≤ C) :
    klDiv ((μP ⊗ₘ policy) ⊗ₘ obsP) ((μQ ⊗ₘ policy) ⊗ₘ obsQ) ≤ klDiv μP μQ + C := by
  rw [round_kl_eq μP μQ policy obsP obsQ]
  exact add_le_add le_rfl hcond

/-! ## The horizon -/

/-- **The horizon bound.**  Given the two worlds' history laws round by round, a per-round
increase of at most `C`, and no divergence before the first query, `n` rounds cost at most
`n * C`.  Composed with `round_kl_le`, this is the transcript bound for any randomised
adaptive policy. -/
theorem kl_le_of_rounds {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (P Q : ∀ n, Measure (H n)) (C : ℝ≥0∞)
    (h0 : klDiv (P 0) (Q 0) = 0)
    (hstep : ∀ n, klDiv (P (n + 1)) (Q (n + 1)) ≤ klDiv (P n) (Q n) + C) :
    ∀ n, klDiv (P n) (Q n) ≤ (n : ℝ≥0∞) * C := by
  intro n
  induction n with
  | zero => rw [h0]; simp
  | succ n ih =>
      calc klDiv (P (n + 1)) (Q (n + 1))
          ≤ klDiv (P n) (Q n) + C := hstep n
        _ ≤ (n : ℝ≥0∞) * C + C := add_le_add ih le_rfl
        _ = ((n + 1 : ℕ) : ℝ≥0∞) * C := by push_cast; ring

/-- **No divergence before the first query**, which is the induction's base case: the two
worlds' empty histories are the same law. -/
theorem kl_start_zero {H : Type*} [MeasurableSpace H] (μ : Measure H) [SigmaFinite μ] :
    klDiv μ μ = 0 := klDiv_self μ

/-! ## Audit -/

#print axioms policy_contributes_nothing
#print axioms round_kl_eq
#print axioms round_kl_le
#print axioms kl_le_of_rounds
#print axioms kl_start_zero

end CIGAMF.P13.PaperBKernel
