import Mathlib

/-! # Support: the two pointwise facts that give the safe-decision exponent.

`scripts/P13_support_decide_exponent.py` replaces the inclusion-exclusion route with
the one-tip-per-class event:
    k0 (1-s)^N  <=  R_dec  <=  B (1-s)^N,   k0 = min_i 1/(a_i+1),  B = prod_i b_i,
checked against the exact joint law on 5 configurations x 7 transcript lengths, 105
exact rational checks.  The probabilistic half is the event "one fixed tip per class
stays unseen", of probability exactly `(1-s)^N`.  The DETERMINISTIC half is two
pointwise inequalities about the loss, and those are what this file proves.

## WHAT IS PROVED

* `frac_le_self` — `L/(a+L) ≤ L` whenever `1 ≤ a` and `0 ≤ L`.  This is what turns
  the loss into a count and lets the upper bound be a tuple count.
* `min_le_prod` — for non-negative integers, `min_i L_i ≤ ∏_i L_i` (both sides vanish
  together when some `L_i = 0`).  With `frac_le_self` this gives
  `min_i L_i/(a_i+L_i) ≤ ∏_i L_i`, whose expectation is `B (1-s)^N`.
* `one_le_frac_lower` — on the event every `L_i ≥ 1`, `L_i/(a_i+L_i) ≥ 1/(a_i+1)`,
  so the loss is at least `k0`.  That is the lower bound's pointwise half.
* `decide_bracket_pointwise` — the two together, as one statement about a profile.

## WHAT THIS DOES NOT ESTABLISH

- The probability `(1-s)^N` of the one-tip-per-class event is not derived here; it is
  checked against the exact law by the script, and the counting half is
  `LeanSupportTupleCountV1.prod_card_eq_tuples`.
- The K-class posterior/minimax step is not re-derived; `passive_minimax` in
  `LeanSupportBayesMinimaxV1` is the one-class statement.
- Nothing here mentions recovery; that side is `LeanSupportRecoverySandwichV1`.
-/

namespace CIGAMF.P13.SupportDecideExponent

open Finset

theorem frac_le_self (a L : ℝ) (ha : 1 ≤ a) (hL : 0 ≤ L) : L/(a + L) ≤ L := by
  have hpos : 0 < a + L := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith

theorem one_le_frac_lower (a L : ℝ) (ha : 0 ≤ a) (hL : 1 ≤ L) :
    1/(a + 1) ≤ L/(a + L) := by
  have h1 : (0:ℝ) < a + 1 := by linarith
  have h2 : (0:ℝ) < a + L := by linarith
  have key : L/(a + L) - 1/(a + 1) = a*(L - 1)/((a + L)*(a + 1)) := by
    field_simp
    ring
  have hnn : 0 ≤ a*(L - 1)/((a + L)*(a + 1)) :=
    div_nonneg (mul_nonneg ha (by linarith)) (le_of_lt (mul_pos h2 h1))
  linarith [key, hnn]

theorem min_le_prod {ι : Type*} [Fintype ι] [Nonempty ι] (L : ι → ℕ) :
    ((univ : Finset ι).inf' univ_nonempty L) ≤ ∏ i, L i := by
  classical
  by_cases h : ∃ i, L i = 0
  · obtain ⟨i, hi⟩ := h
    have : ((univ : Finset ι).inf' univ_nonempty L) ≤ 0 :=
      le_of_le_of_eq (Finset.inf'_le _ (mem_univ i)) hi
    omega
  · push_neg at h
    have hone : ∀ i, 1 ≤ L i := fun i => Nat.one_le_iff_ne_zero.mpr (h i)
    obtain ⟨i₀, -, hi₀⟩ := (univ : Finset ι).exists_min_image L univ_nonempty
    have hmin : ((univ : Finset ι).inf' univ_nonempty L) = L i₀ :=
      le_antisymm (Finset.inf'_le _ (mem_univ i₀))
        (Finset.le_inf' _ _ fun i _ => hi₀ i (mem_univ i))
    rw [hmin]
    calc L i₀ = L i₀ * 1 := by ring
      _ ≤ L i₀ * ∏ i ∈ univ.erase i₀, L i := by
          refine Nat.mul_le_mul_left _ ?_
          exact Finset.one_le_prod' fun i _ => hone i
      _ = ∏ i, L i := Finset.mul_prod_erase _ _ (mem_univ i₀)

/-- Both halves at once, at a fixed unseen profile. -/
theorem decide_bracket_pointwise {ι : Type*} [Fintype ι] [Nonempty ι]
    (a L : ι → ℝ) (ha : ∀ i, 1 ≤ a i) (hL : ∀ i, 1 ≤ L i) :
    ((univ : Finset ι).inf' univ_nonempty (fun i => 1/(a i + 1)))
        ≤ (univ : Finset ι).inf' univ_nonempty (fun i => L i/(a i + L i))
    ∧ (univ : Finset ι).inf' univ_nonempty (fun i => L i/(a i + L i))
        ≤ (univ : Finset ι).inf' univ_nonempty L := by
  constructor
  · refine Finset.le_inf' _ _ fun i _ => ?_
    exact le_trans (Finset.inf'_le _ (mem_univ i))
      (one_le_frac_lower (a i) (L i) (by linarith [ha i]) (hL i))
  · obtain ⟨i₀, -, hi₀⟩ := (univ : Finset ι).exists_min_image L univ_nonempty
    have hmin : (univ : Finset ι).inf' univ_nonempty L = L i₀ :=
      le_antisymm (Finset.inf'_le _ (mem_univ i₀))
        (Finset.le_inf' _ _ fun i _ => hi₀ i (mem_univ i))
    rw [hmin]
    exact le_trans (Finset.inf'_le _ (mem_univ i₀))
      (frac_le_self (a i₀) (L i₀) (ha i₀) (by linarith [hL i₀]))

#print axioms frac_le_self
#print axioms one_le_frac_lower
#print axioms min_le_prod
#print axioms decide_bracket_pointwise

end CIGAMF.P13.SupportDecideExponent
