import «LeanFunctionalPairFlipCostV1»

/-! # Functional F05: the scalar proxy is wrong in BOTH directions, by no constant.

`J_scalar` is the pair-flip value at the CURRENT extrema with the ordering constraints
dropped; `J_old` is the QP in the current-extrema region; `J_full` is the infimum over the
whole alternative set, with the extrema free in either relation.  By inclusion of feasible
sets `J_scalar ≤ J_old` and `J_full ≤ J_old`, and there is NO general order between
`J_scalar` and `J_full`.

This file proves that last sentence quantitatively, on two explicit two-relation,
three-action families.  No optimiser is used, no world is sampled, and no seed is drawn:
each bound is an explicit feasible alternative on one side and an elementary lower bound
on the other.

Energy: `E(λ) = ½ ∑_{r,a} α_{r,a} (λ_{r,a} − θ_{r,a})²`, precisions `α = w/σ² > 0`.
Capacity of a relation is the range of its cells.  Top-1 is relation `i`.

## FAMILY 1 — cheap middle cell.  `J_full / J_scalar → 0`.

    θ_i = (0, 1, 1/2),   α_i = (1, 1, 1)
    θ_j = (0, 1/2, 1/4), α_j = (1, 1, η)

`J_scalar = 1/32`.  Raising ONLY the third cell of `j` from `1/4` to `1` makes the two
capacities equal, at cost `9η/32`.  So `0 ≤ J_full/J_scalar ≤ 9η → 0`.

## FAMILY 2 — old max cheap, runner-up expensive.  `J_full / J_scalar → ∞`.

    θ_i = (0, 1, 3/4),   α_i = (1, η, 1)
    θ_j = (0, 1/2, 1/4), α_j = (1, 1, 1)

`J_scalar = η / (8(1+3η))`.  Any capacity-inverting alternative admits a `z` between the
two new capacities; shrinking `i` below `z` costs at least `[3/4−z]₊²/4` on its two
expensive cells, opening `j` above `z` costs at least `[z−1/2]₊²/4`, and the two positive
parts always sum to at least `1/4`.  Hence `J_full ≥ 1/128` and
`J_full/J_scalar ≥ (1+3η)/(16η) → ∞`.

## WHAT IS PROVED

* `cap_i1`, `cap_j1`, `cap_j1_alt` — the capacities, computed.
* `family1_alt_cost`, `family1_alt_ties` — the explicit alternative and its energy.
* `family1_scalar_value`, `family1_full_le`, `family1_ratio` — the vanishing ratio.
* `positive_parts_sum` — `[3/4−z]₊ + [z−1/2]₊ ≥ 1/4` for every `z`.
* `family2_cell_lower`, `family2_full_ge` — the `1/128` floor, from the two cell lower
  bounds summed.
* `family2_scalar_value`, `family2_ratio` — the diverging ratio.
* `scalar_not_upper_to_any_constant`, `scalar_not_lower_to_any_constant` — **the two
  headline statements**: for every constant `C > 0` there is a member of family 1 with
  `J_full < J_scalar / C`, and a member of family 2 with `J_full > C · J_scalar`.

## WHAT THIS DOES NOT ESTABLISH

- Nothing here proves the oracle equality `J_full = min_{i,j} inf_z [S_i(z) + E_j(z)]`.
  These are two families, not the general decomposition.
- `family1_full_le` is an UPPER bound on `J_full` from one exhibited alternative; the
  infimum could be smaller, which only strengthens the conclusion.
- `family2_full_ge` bounds the cost of any alternative that INVERTS the capacities.  The
  closed alternative set uses `≥`, the usual tie convention, and that is what is bounded.
- Free response table, known variance, positive precision.  Under realizability coupling
  the cost does not separate across relations and none of this is claimed.
-/

namespace CIGAMF.P13.FunctionalScalarProxyFails

open CIGAMF.P13.FunctionalPairFlipCost

noncomputable section

/-- Range of a three-cell relation. -/
def cap3 (a b c : ℝ) : ℝ := max (max a b) c - min (min a b) c

/-! ## Family 1: capacities and the explicit alternative. -/

theorem cap_i1 : cap3 0 1 (1/2) = 1 := by unfold cap3; norm_num
theorem cap_j1 : cap3 0 (1/2) (1/4) = 1/2 := by unfold cap3; norm_num
theorem cap_j1_alt : cap3 0 (1/2) 1 = 1 := by unfold cap3; norm_num

/-- **The explicit alternative ties the two capacities**, so it lies in the closed
alternative set. -/
theorem family1_alt_ties : cap3 0 (1/2) 1 = cap3 0 1 (1/2) := by
  rw [cap_j1_alt, cap_i1]

/-- **Its energy**: only the third cell of `j` moves, from `1/4` to `1`. -/
theorem family1_alt_cost (eta : ℝ) :
    (1/2) * eta * (1 - 1/4) ^ 2 = 9 * eta / 32 := by ring

/-- **The scalar proxy value.**  Gap `1/2` across four unit-precision cells. -/
theorem family1_scalar_value :
    (1/2 : ℝ) ^ 2 / (2 * (1 + 1 + 1 + 1)) = 1 / 32 := by norm_num

/-- `J_full` is at most the exhibited alternative's energy. -/
theorem family1_full_le (Jfull eta : ℝ) (halt : Jfull ≤ (1/2) * eta * (1 - 1/4) ^ 2) :
    Jfull ≤ 9 * eta / 32 := by
  rwa [family1_alt_cost eta] at halt

/-- **The ratio vanishes**: `J_full / J_scalar ≤ 9η`. -/
theorem family1_ratio (Jfull eta : ℝ) (heta : 0 < eta)
    (hJ : Jfull ≤ 9 * eta / 32) (hJ0 : 0 ≤ Jfull) :
    Jfull / (1 / 32 : ℝ) ≤ 9 * eta := by
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1/32)]
  linarith

/-! ## Family 2: the two-sided floor. -/

/-- **The two positive parts always sum to at least `1/4`.**  Whatever `z` the alternative
chooses, either the shrink or the opening is expensive. -/
theorem positive_parts_sum (z : ℝ) :
    (1/4 : ℝ) ≤ max (3/4 - z) 0 + max (z - 1/2) 0 := by
  rcases le_or_gt z (1/2) with h | h
  · have h1 : max (3/4 - z) 0 = 3/4 - z := by
      rw [max_eq_left]; linarith
    rw [h1]
    have h2 : (0:ℝ) ≤ max (z - 1/2) 0 := le_max_right _ _
    linarith
  · rcases le_or_gt z (3/4) with h' | h'
    · have h1 : max (3/4 - z) 0 = 3/4 - z := by rw [max_eq_left]; linarith
      have h2 : max (z - 1/2) 0 = z - 1/2 := by rw [max_eq_left]; linarith
      rw [h1, h2]; linarith
    · have h2 : max (z - 1/2) 0 = z - 1/2 := by rw [max_eq_left]; linarith
      have h1 : (0:ℝ) ≤ max (3/4 - z) 0 := le_max_right _ _
      rw [h2]; linarith

/-- Each cell pair's cost, from `pair_flip_lower` with two unit-variance cells. -/
theorem family2_cell_lower (gap x y : ℝ) (hg : 0 ≤ gap) (hcross : gap ≤ x + y) :
    gap ^ 2 / 4 ≤ energy 1 1 x y := by
  have h := pair_flip_lower 1 1 gap x y (by norm_num) (by norm_num) hg hcross
  norm_num at h
  linarith

/-- **The `1/128` floor.**  Summing the two cell lower bounds over any `z`. -/
theorem family2_full_ge (z : ℝ) :
    (1/128 : ℝ) ≤ (max (3/4 - z) 0) ^ 2 / 4 + (max (z - 1/2) 0) ^ 2 / 4 := by
  set a := max (3/4 - z) 0 with ha
  set b := max (z - 1/2) 0 with hb
  have ha0 : 0 ≤ a := le_max_right _ _
  have hb0 : 0 ≤ b := le_max_right _ _
  have hsum : (1/4 : ℝ) ≤ a + b := positive_parts_sum z
  nlinarith [sq_nonneg (a - b), ha0, hb0, hsum]

/-- **The scalar proxy value** for family 2: gap `1/2` across precisions `η,1,1,1`. -/
theorem family2_scalar_value (eta : ℝ) (heta : 0 < eta) :
    (1/2 : ℝ) ^ 2 / (2 * (1/eta + 1 + 1 + 1)) = eta / (8 * (1 + 3 * eta)) := by
  have h1 : (0:ℝ) < 1 + 3 * eta := by linarith
  have hne : eta ≠ 0 := ne_of_gt heta
  field_simp
  ring

/-- **The ratio diverges**: `J_full / J_scalar ≥ (1+3η)/(16η)`. -/
theorem family2_ratio (Jfull eta : ℝ) (heta : 0 < eta) (hJ : (1/128 : ℝ) ≤ Jfull) :
    (1 + 3 * eta) / (16 * eta) ≤ Jfull / (eta / (8 * (1 + 3 * eta))) := by
  have h1 : (0:ℝ) < 1 + 3 * eta := by linarith
  have hs : (0:ℝ) < eta / (8 * (1 + 3 * eta)) := by positivity
  rw [le_div_iff₀ hs]
  have hrw : (1 + 3 * eta) / (16 * eta) * (eta / (8 * (1 + 3 * eta))) = 1 / 128 := by
    field_simp
    ring
  rw [hrw]
  exact hJ

/-! ## The two headline statements. -/

/-- **The scalar proxy is not an upper bound up to any constant.**  For every `C > 0`
family 1 contains a member whose true value is below `J_scalar / C`. -/
theorem scalar_not_upper_to_any_constant (C : ℝ) (hC : 0 < C) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ 9 * eta / 32 < (1 / 32 : ℝ) / C := by
  refine ⟨min 1 (1 / (10 * C)), ?_, min_le_left _ _, ?_⟩
  · exact lt_min (by norm_num) (by positivity)
  · have hle : min 1 (1 / (10 * C)) ≤ 1 / (10 * C) := min_le_right _ _
    have hkey : 9 * min 1 (1 / (10 * C)) * C ≤ 9 / 10 := by
      have h1 : min 1 (1 / (10 * C)) * C ≤ (1 / (10 * C)) * C :=
        mul_le_mul_of_nonneg_right hle hC.le
      have h2 : (1 / (10 * C)) * C = 1 / 10 := by
        field_simp
      nlinarith [h1, h2]
    rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 32) hC]
    nlinarith [hkey]

/-- **The scalar proxy is not a lower bound up to any constant.**  For every `C > 0`
family 2 contains a member whose true value exceeds `C · J_scalar`. -/
theorem scalar_not_lower_to_any_constant (C : ℝ) (hC : 0 < C) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ C * (eta / (8 * (1 + 3 * eta))) < (1 / 128 : ℝ) := by
  refine ⟨min 1 (1 / (100 * C)), lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  set e := min 1 (1 / (100 * C)) with he
  have he0 : 0 < e := lt_min (by norm_num) (by positivity)
  have hele : e ≤ 1 / (100 * C) := min_le_right _ _
  have hden : (0:ℝ) < 8 * (1 + 3 * e) := by linarith
  have hbound : e / (8 * (1 + 3 * e)) ≤ e / 8 := by
    apply div_le_div_of_nonneg_left he0.le (by norm_num) (by linarith)
  calc C * (e / (8 * (1 + 3 * e))) ≤ C * (e / 8) := by
        exact mul_le_mul_of_nonneg_left hbound hC.le
    _ ≤ C * ((1 / (100 * C)) / 8) := by
        have : e / 8 ≤ (1 / (100 * C)) / 8 := by linarith
        exact mul_le_mul_of_nonneg_left this hC.le
    _ < (1 / 128 : ℝ) := by
        have hCne : C ≠ 0 := ne_of_gt hC
        have hval : C * ((1 / (100 * C)) / 8) = 1 / 800 := by
          field_simp
          norm_num
        rw [hval]
        norm_num

#print axioms cap_i1
#print axioms cap_j1
#print axioms family1_alt_ties
#print axioms family1_alt_cost
#print axioms family1_scalar_value
#print axioms family1_full_le
#print axioms family1_ratio
#print axioms positive_parts_sum
#print axioms family2_cell_lower
#print axioms family2_full_ge
#print axioms family2_scalar_value
#print axioms family2_ratio
#print axioms scalar_not_upper_to_any_constant
#print axioms scalar_not_lower_to_any_constant

end

end CIGAMF.P13.FunctionalScalarProxyFails
