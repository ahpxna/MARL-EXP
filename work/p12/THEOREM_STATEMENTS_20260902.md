# P13 Novelty-Branch Theorem Statements — 2026-09-02

Pinned environment: Lean `4.34.0-rc2`; Mathlib
`1f495c611d05d2215058cd77c7897d625bc3b445`.

All results listed as compiled have zero `sorry`, zero `admit`, and no user
axioms.  The frozen P12 baseline is unchanged.

## D6 normalization boundary

- `badCell2_not_atMost_one`: an exact balanced two-coordinate cell with an
  unnormalised row-mass-two reference violates uniform constant `m-1=1` even
  though its numerical world is additive and every mixed difference is zero.
- `balancedDecisionInteractionBound_type0_false`: the universe-zero instance
  of the legacy unnormalised `BalancedDecisionInteractionBound` is false.
- `scaledPointMass2_not_normalized`: the counterexample's joint reference mass
  is exactly four.  Thus this does not refute the nonnegative normalized law.
- `normalized_all_iff_balanced`: under nonnegative normalized product weights,
  the all-cell `m-1` law is equivalent to its balanced-complement branch; the
  latter remains the precise open D6 target.
- `decisionLinearFunctional_eq_cyclePart_add_remainder`: exposes the exact
  cycle/remainder split of any supplied canonical active-cell certificate.
- `canonicalRemainder_eq_active_cell_cone` and
  `canonicalRemainder_nonpos_of_valid_cell`: the remainder is an exact
  nonnegative combination of the permitted polyhedral active-cell atoms and
  is nonpositive on a valid cell.
- `normalized_balanced_law_of_canonical_completion`: if every normalized
  balanced cell admits a canonical certificate of mass at most `m-1`, the
  normalized balanced law follows.  The universal completion premise is not
  proved.

## Structural finite lower bounds

- `STRUCT_SCALAR_CHI5_prefix_cover_not_at_most_four`: an actual seven-relation,
  two-support-point `selectedRadius` instance has five forced pairwise
  incomparable unique optima; four rankings cannot cover all budget layers.

## Structural unbounded family

- `staircaseBlock_sum_zero`: every designated positive-prefix/negative-
  staircase omitted block has identically zero aggregate response.
- `sum_zero_set_eq_empty_or_staircaseBlock`: for positive parameter `r`, these
  designated blocks are the only nonempty omitted sets with zero aggregate
  response.
- `staircaseSelected_unique_optimal`: at its cardinality, every designated
  retained set is the unique zero-radius optimum of the actual supportOsc
  objective.
- `STRUCT_UNBOUNDED_staircase_prefix_dimension_ge`: for every `r>0`,
  `PrefixCoverDimensionAtMost (selectedRadius staircaseF) 0 (r-1)` is false.
  Equivalently, this actual finite-support family has
  `chi_prefix(F_r,0) >= r`.
- `STRUCT_UNIVERSAL_prefix_cover_at_most_card_add_one`: every finite objective
  on `I` admits a zero-tolerance prefix-cover menu containing at most
  `Fintype.card I + 1` rankings.
- `STRUCT_UNBOUNDED_staircase_linear_sandwich`: for every `r>0`, the actual
  staircase supportOsc family satisfies
  `r <= chi_prefix(F_r,0) <= 2*r+1`; this is a linear sandwich, not an exact
  equality claim.
- `STRUCT_staircase_r6_not_at_most_five`: explicit specialization giving
  `chi_prefix >= 6` on `StairRel 6`, a 12-relation ground set.  There is no
  Fin-8/`chi_prefix >= 6` theorem in this branch.

Open boundaries: equality `chi_prefix(F_r,0)=r`, positive-tolerance menu
regret, and the normalized universal balanced D6 law are not claimed.
