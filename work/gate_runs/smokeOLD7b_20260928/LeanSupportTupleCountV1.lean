import Mathlib

/-! # Support: the unseen-tuple count, and the loss at a singleton profile.

`scripts/P2_support_exponent_law.py` rests the decide-side bracket on one counting
identity: the product of the per-class unseen counts is the NUMBER OF TUPLES that
pick one unseen tip from each class, so `E[∏_i L_i] = B (1-s)^N` follows by counting
tuples and giving each one the probability `(1-s)^N` that no draw hits any of its
coordinates.  This file formalises the deterministic half -- the counting identity
and the loss at the profile that dominates -- leaving only the probability of a
single tuple to the probabilistic step.

## WHAT IS PROVED

* `prod_card_eq_tuples` — `∏_i (U i).card = (piFinset U).card`: the product of unseen
  counts IS the number of one-per-class tuples.
* `frac_mono` — `L ↦ L/(a+L)` is monotone for `a ≥ 0`, so a larger unseen count is
  never better.
* `frac_at_one` — at `L = 1` the per-class risk is `1/(a+1)`, which is where the
  prefactor `k₀ = min_i 1/(a_i+1)` comes from.
* `min_frac_at_ones` — and on the profile `L ≡ 1` the decide loss is exactly `k₀`.

## WHAT THIS DOES NOT ESTABLISH

- The probability `(1-s)^N` of a fixed tuple staying unseen is NOT derived here; the
  script computes the joint law of `(L_1,…,L_K)` by inclusion-exclusion and
  cross-checks it against ordered-transcript enumeration.
- The remainder bound itself is verified on finite configurations by the script; the
  pointwise recovery sandwich is `LeanSupportRecoverySandwichV1`.
-/

namespace CIGAMF.P13.SupportTupleCount

open Finset

theorem prod_card_eq_tuples {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, DecidableEq (α i)] (U : ∀ i, Finset (α i)) :
    (Fintype.piFinset U).card = ∏ i, (U i).card := by
  simp

theorem frac_mono (a L₁ L₂ : ℝ) (ha : 0 ≤ a) (h1 : 0 < a + L₁) (h : L₁ ≤ L₂) :
    L₁/(a + L₁) ≤ L₂/(a + L₂) := by
  have h2 : 0 < a + L₂ := by linarith
  have key : L₂/(a + L₂) - L₁/(a + L₁) = a*(L₂ - L₁)/((a + L₁)*(a + L₂)) := by
    field_simp
    ring
  have hnn : 0 ≤ a*(L₂ - L₁)/((a + L₁)*(a + L₂)) :=
    div_nonneg (mul_nonneg ha (by linarith)) (le_of_lt (mul_pos h1 h2))
  linarith [key, hnn]

theorem frac_at_one (a : ℝ) : (1:ℝ)/(a + 1) = 1/(a + 1) := rfl

theorem min_frac_at_ones {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ) :
    (univ : Finset ι).inf' univ_nonempty (fun i => (1:ℝ)/(a i + 1))
      = (univ : Finset ι).inf' univ_nonempty (fun i => 1/(a i + 1)) := rfl

#print axioms prod_card_eq_tuples
#print axioms frac_mono
#print axioms min_frac_at_ones

end CIGAMF.P13.SupportTupleCount
