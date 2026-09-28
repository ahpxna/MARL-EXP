import «LeanSupportSamplingLawV1»

/-! # Support: the equivariant decoder, CONSTRUCTED -- the last hypothesis of the
minimax lift.

`LeanSupportSamplingLawV1.minimax_eq_of_constant` lifts a Bayes bound to a minimax
bound, but it TAKES a rule whose risk is constant across worlds.  Nothing constructed
such a rule.  This file does.

## THE DECODER

A class has `a` safe and `b` unsafe tips in a finite set `T`, `|T| = a + b`.  A world
is the unsafe set `W ⊆ T` with `|W| = b`.  Observations reveal only unsafe tips, so a
transcript gives `R ⊆ W`.  The decoder names a tip drawn uniformly from the UNEXPLORED
set `T \ R`, and errs exactly when that tip is unsafe.

## WHY IT IS EQUIVARIANT

The number of unsafe tips still hidden is `|W \ R| = b - |R|` -- the SAME for every
world compatible with the transcript, because every compatible world has exactly `b`
unsafe tips and contains all the revealed ones.  So the decoder's conditional risk

    (b - |R|) / (a + b - |R|)

is a function of the TRANSCRIPT ALONE.  That is equivariance, and it is exactly the
constant-risk hypothesis `minimax_eq_of_constant` needs.

## WHAT IS PROVED

* `hidden_count_world_free` — `|W \ R| = b - |R|` for every compatible world.
* `decoder_risk_world_free` — **the decoder's risk is the same number in every
  compatible world**, so it is determined by the transcript.
* `decoder_risk_eq_L_over_aL` — and that number is `L/(a+L)` with `L = b - |R|` the
  unseen unsafe count and `a` the safe count: the quantity the decide law is stated in.
* `bayes_is_minimax` — for THIS decoder the Bayes risk equals its worst-case risk,
  because its risk is the same number in every world.

## WHAT THIS DOES NOT ESTABLISH

- **The minimax LOWER bound.**  What is proved is that this decoder's Bayes risk equals
  its worst-case risk, so the stated value is an UPPER bound on the problem's minimax
  risk.  Turning it into a lower bound needs the decoder to be BAYES-OPTIMAL -- that no
  rule does better -- and that is NOT proved here.  `fixed_tip_unsafe_fraction` gives
  the per-tip posterior, but the optimality over all decision rules is not formalised.
  So "Bayes = minimax for the PROBLEM" does not follow from these lemmas.
- One class.  The `K`-class decoder picks the class minimising `L_i/(a_i+L_i)` and then
  applies this rule; the argmin is a function of the transcript, so the same argument
  applies, but the product structure is not re-proved here.
- Optimality of this decoder among all rules is the Bayes step
  (`fixed_tip_unsafe_fraction`), not this file.
-/

namespace CIGAMF.P13.SupportEquivariantDecoder

open Finset CIGAMF.P13.SupportSamplingLaw

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- **The hidden count does not depend on the world.**  Every world compatible with the
transcript has exactly `b` unsafe tips and contains all the revealed ones, so the number
still hidden is `b - |R|` in all of them. -/
theorem hidden_count_world_free (W R : Finset T) (b : ℕ)
    (hW : W.card = b) (hRW : R ⊆ W) :
    (W \ R).card = b - R.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.2 hRW, hW]

/-- **The decoder's risk is world-free.**  Two worlds compatible with the same
transcript give the decoder the same error probability. -/
theorem decoder_risk_world_free (W₁ W₂ R : Finset T) (b : ℕ)
    (hW₁ : W₁.card = b) (hW₂ : W₂.card = b) (h₁ : R ⊆ W₁) (h₂ : R ⊆ W₂)
    (U : Finset T) :
    ((W₁ \ R).card : ℝ) / U.card = ((W₂ \ R).card : ℝ) / U.card := by
  rw [hidden_count_world_free W₁ R b hW₁ h₁, hidden_count_world_free W₂ R b hW₂ h₂]

/-- …and that risk is `L/(a+L)` with `L` the unseen unsafe count and `a` the safe count:
the unexplored set is `T \ R`, of size `a + L`. -/
theorem decoder_risk_eq_L_over_aL (W R : Finset T) (a b : ℕ)
    (hW : W.card = b) (hRW : R ⊆ W) (hT : Fintype.card T = a + b)
    (hle : R.card ≤ b) :
    (((W \ R).card : ℝ)) / ((univ \ R).card : ℝ)
      = ((b - R.card : ℕ) : ℝ) / ((a : ℝ) + ((b - R.card : ℕ) : ℝ)) := by
  classical
  have hsub : R ⊆ (univ : Finset T) := Finset.subset_univ R
  have hcard : ((univ : Finset T) \ R).card = a + (b - R.card) := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hT]
    omega
  rw [hidden_count_world_free W R b hW hRW, hcard]
  push_cast
  ring

/-- **The lift.**  A decoder whose risk is the constant `r` in every world has minimax
risk exactly `r`, and the Bayes risk of any prior is at most the minimax risk.  So for
this decoder the two coincide. -/
theorem bayes_is_minimax {World : Type*} [Fintype World] [Nonempty World]
    (pri R : World → ℝ) (r : ℝ)
    (hpi : ∀ w, 0 ≤ pri w) (hsum : ∑ w, pri w = 1)
    (hconst : ∀ w, R w = r) :
    (∑ w, pri w * R w) = r ∧ (univ : Finset World).sup' univ_nonempty R = r := by
  constructor
  · simp only [hconst]
    rw [← Finset.sum_mul, hsum, one_mul]
  · exact minimax_eq_of_constant R r hconst

#print axioms hidden_count_world_free
#print axioms decoder_risk_world_free
#print axioms decoder_risk_eq_L_over_aL
#print axioms bayes_is_minimax

end CIGAMF.P13.SupportEquivariantDecoder
