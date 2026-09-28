import Mathlib

/-! # MASTER: the ACTIVE SET of the whole game, and why a single alternative cannot
carry the acquisition threshold.

`LeanMasterAnchorCertificateV1` proves both sides of the anchor price threshold for
ONE alternative with given `D_u, M_u, K`.  `scripts/P8_master_active_set.py` shows on
a concrete four-item instance what happens when the game has more than one:

  * the anchor-free optimum has an ACTIVE SET of size 2 out of 3, and the dual weights
    sit on exactly those two;
  * the whole-game threshold is `c0* = 0.118`, and below it the anchor is bought
    (`x0 = 1.72`, value `0.013773 -> 0.014951`);
  * but for EVERY single alternative on its own the threshold is ZERO -- the optimal
    one-alternative design already splits weight so that `M_u = 0`, and then
    `I_u = D_u - M_u^2/(2K) = D_u` does not depend on the anchor at all.

So the positive threshold is not a property of any alternative; it exists because the
ACTIVE alternatives demand incompatible offset cancellations.  This file proves the
three general facts that turn that observation into a rule.

## WHAT IS PROVED

* `complementary_slackness` — if `V` is a lower bound on every `I u`, `lam` is a
  probability vector, and the `lam`-average of `I` is at most `V`, then every `u`
  with `lam u > 0` has `I u = V`.  The support of any tight dual lies in the ACTIVE
  SET; this is what lets a solver's weights be read as an active set.
* `dual_support_active` — the same conclusion packaged from the hypotheses
  `dual_bound` actually produces: a primal attaining `V` together with a dual capping
  the game at `V`.
* `anchor_worthless_when_offset_cancels` — if a design has `M u = 0` then the profiled
  information is `D u` for EVERY anchor exposure: buying exposure changes nothing.
* `cancelling_design_exists` — and for a single alternative such a design always
  exists as soon as two queries carry `d` of opposite sign: the explicit weights
  `(-d₂, d₁)/(d₁ - d₂)` give `M = 0`.  Hence the one-alternative threshold is zero,
  which is what the script measures.
* `value_improves_iff` — the min over alternatives rises above `V` exactly when EVERY
  alternative does: `min_improves` needs all of them, and `one_bad_blocks` shows a
  single active alternative that fails to improve caps the new value at `V`.  So the
  acquisition rule must be run against the whole active set.

## WHAT THIS DOES NOT ESTABLISH

- No derivative is taken.  `value_improves_iff` compares two given information
  vectors; the statement that a small purchase produces such a vector is the analytic
  step and is not formalised.
- `cancelling_design_exists` is about one alternative and two queries; it explains why
  the one-alternative threshold vanishes on the script's instance, and is not a claim
  about every instance.
- The numbers `c0* = 0.118`, the active set and the certificate come from the script's
  LP re-checked in exact rationals, not from Lean.
-/

namespace CIGAMF.P13.MasterActiveSet

open Finset

noncomputable section

variable {U : Type*} [Fintype U] [Nonempty U]

/-- The support of a tight dual lies in the active set. -/
theorem complementary_slackness (I lam : U → ℝ) (V : ℝ)
    (hV : ∀ u, V ≤ I u) (hl0 : ∀ u, 0 ≤ lam u) (hl1 : ∑ u, lam u = 1)
    (htight : ∑ u, lam u * I u ≤ V) :
    ∀ u, 0 < lam u → I u = V := by
  have hge : ∑ u, lam u * V ≤ ∑ u, lam u * I u :=
    Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hV u) (hl0 u)
  have hVsum : ∑ u, lam u * V = V := by
    rw [← Finset.sum_mul, hl1, one_mul]
  have hzero : ∑ u, lam u * (I u - V) = 0 := by
    have : ∑ u, lam u * (I u - V) = (∑ u, lam u * I u) - ∑ u, lam u * V := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [this, hVsum]
    linarith [hge, htight, hVsum]
  have hnn : ∀ u ∈ (univ : Finset U), 0 ≤ lam u * (I u - V) :=
    fun u _ => mul_nonneg (hl0 u) (by linarith [hV u])
  intro u hu
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero u (mem_univ u)
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (ne_of_gt hu)
  · linarith

/-- The same conclusion from what a primal/dual pair actually supplies. -/
theorem dual_support_active (I lam : U → ℝ) (V : ℝ)
    (hl0 : ∀ u, 0 ≤ lam u) (hl1 : ∑ u, lam u = 1)
    (u0 : U) (hattain : I u0 = V) (hmin : ∀ u, I u0 ≤ I u)
    (hcap : ∑ u, lam u * I u ≤ V) :
    ∀ u, 0 < lam u → I u = V :=
  complementary_slackness I lam V (fun u => hattain ▸ hmin u) hl0 hl1 hcap

/-- If the design already cancels the offset for an alternative, the anchor cannot
change that alternative's information, at any exposure and any price. -/
theorem anchor_worthless_when_offset_cancels (D K s : ℝ) (hM : (0:ℝ) = 0) :
    D - (0:ℝ)^2/(2*(K + s)) = D := by
  simp

/-- And for ONE alternative such a design exists whenever two queries carry `d` of
opposite sign: the weights below are non-negative, sum to one, and kill `M`. -/
theorem cancelling_design_exists (d₁ d₂ : ℝ) (h₁ : 0 < d₁) (h₂ : d₂ < 0) :
    let a₁ := (-d₂)/(d₁ - d₂)
    let a₂ := d₁/(d₁ - d₂)
    0 ≤ a₁ ∧ 0 ≤ a₂ ∧ a₁ + a₂ = 1 ∧ a₁*d₁ + a₂*d₂ = 0 := by
  have hden : 0 < d₁ - d₂ := by linarith
  have hn₂ : 0 < -d₂ := by linarith
  refine ⟨le_of_lt (div_pos hn₂ hden), le_of_lt (div_pos h₁ hden), ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring

/-- The minimum rises only if EVERY alternative rises. -/
theorem min_improves (I' : U → ℝ) (V : ℝ) (hall : ∀ u, V < I' u) :
    V < (univ : Finset U).inf' univ_nonempty I' := by
  obtain ⟨u₀, -, hu₀⟩ :=
    (univ : Finset U).exists_min_image I' univ_nonempty
  have hle : (univ : Finset U).inf' univ_nonempty I' = I' u₀ :=
    le_antisymm (Finset.inf'_le _ (mem_univ u₀))
      (Finset.le_inf' _ _ fun u _ => hu₀ u (mem_univ u))
  rw [hle]
  exact hall u₀

/-- And a single alternative that fails to rise caps the new value at `V`. -/
theorem one_bad_blocks (I' : U → ℝ) (V : ℝ) (u0 : U) (hbad : I' u0 ≤ V) :
    (univ : Finset U).inf' univ_nonempty I' ≤ V :=
  le_trans (Finset.inf'_le _ (mem_univ u0)) hbad

/-- Both halves together: the acquisition rule is a statement about the whole active
set, not about any one of its members. -/
theorem value_improves_iff (I' : U → ℝ) (V : ℝ) :
    (V < (univ : Finset U).inf' univ_nonempty I') ↔ (∀ u, V < I' u) := by
  constructor
  · intro h u
    exact lt_of_lt_of_le h (Finset.inf'_le _ (mem_univ u))
  · exact min_improves I' V

#print axioms complementary_slackness
#print axioms dual_support_active
#print axioms anchor_worthless_when_offset_cancels
#print axioms cancelling_design_exists
#print axioms min_improves
#print axioms one_bad_blocks
#print axioms value_improves_iff

end
end CIGAMF.P13.MasterActiveSet
