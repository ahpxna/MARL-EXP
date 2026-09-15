import Mathlib
import «LeanD6ScalarMultiaffineRankOneV1»
import «LeanD6InteractionContrastProfileReductionV1»
import «LeanD6InteractionContrastRankOneMinorsV1»

/-!
# An exact integer witness: StrictTopC + TwoProfile + RankOne does not imply `m-1`

`m = 6`, `|U| = 3`, `k = 3`, corner product reference `q_i = (1,0,0)`.

The world is given in SCALAR MULTIAFFINE NORMAL FORM rather than as a 729-entry
table.  That is not cosmetic: `scalarMultiaffineWorld_allCoordinatesInteractionContrastRankOne`
(already compiled) then delivers rank one at every coordinate ALGEBRAICALLY, with
no enumeration of the 42424 two-by-two profile minors, and the two-profile
property follows because `phi` takes only two values.

Every coefficient is an integer.  The witness was obtained by rounding the
coefficient vector of an exact-rational counterexample inside the 70-dimensional
closed-form fibre basis and clearing denominators; rounding IN THE FIBRE cannot
break rank one, and the decision ratio is positively homogeneous of degree one,
so clearing denominators is exact.

The measured exact values, for reference (NOT yet proved here):

  response spans C = (23,23,23,22,22,22),  selected {0,1,2},  Top-C margin 1
  delta_square = 26,  2D = 131,  (m-1) * delta_square = 130,  so 2D > 5 * delta.

This module deliberately contains ONLY the definitions and the algebraic layer.
The numeric lemmas (`_response_spans`, `_strictTopC`, `_deltaBox_exact`,
`_selectedLoss_exact`, `_violates_five`) are NOT stated here and NOT `sorry`ed:
they are a separate module, because a hole is worse than an absence.
-/

namespace CIGAMF.P13.D6StrictRankOneM6Witness

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6InteractionContrastRankOne
open CIGAMF.P13.D6InteractionContrastProfileReduction
open CIGAMF.P13.D6InteractionContrastRankOneMinors
open CIGAMF.P13.D6ScalarMultiaffineRankOne

/-- Corner (deterministic) product reference: a point mass on action `0` at every
coordinate.  Nonnegative and normalized; positivity is NOT required by Chain D. -/
def cornerQ6 (_i : Fin 6) (u : Fin 3) : ℝ := if u = 0 then 1 else 0

/-- The scalar latent map.  It takes only the two values `0` and `1`, which is
exactly what makes the witness a TWO-PROFILE world. -/
def witnessPhi (_i : Fin 6) (u : Fin 3) : ℝ := if u = 1 then 1 else 0

/-- Coordinate-additive part. -/
def witnessG : Fin 6 → Fin 3 → ℝ
| i, u => match (i : ℕ), (u : ℕ) with
  | 0, 1 => (23 : ℝ)
  | 0, 2 => (0 : ℝ)
  | 1, 1 => (23 : ℝ)
  | 1, 2 => (0 : ℝ)
  | 2, 1 => (23 : ℝ)
  | 2, 2 => (0 : ℝ)
  | 3, 1 => (22 : ℝ)
  | 3, 2 => (0 : ℝ)
  | 4, 1 => (22 : ℝ)
  | 4, 2 => (0 : ℝ)
  | 5, 1 => (0 : ℝ)
  | 5, 2 => (22 : ℝ)
  | _, _ => 0

/-- Constant term. -/
def witnessB : ℝ := -65

/-- Subsets of `Fin 6` as bitmasks, so the tensor core is one flat table. -/
def subsetMask (S : Finset (Fin 6)) : ℕ := S.sum (fun j => 2 ^ (j : ℕ))

/-- The tensor core, indexed by bitmask.  Only orders two and above are used;
every order-zero and order-one contribution is carried by `witnessB` and
`witnessG`. -/
def witnessCoreQ : ℕ → ℚ
  | 3 => (-23 : ℚ)   -- W(0, 1)
  | 5 => (-23 : ℚ)   -- W(0, 2)
  | 6 => (-23 : ℚ)   -- W(1, 2)
  | 7 => (24 : ℚ)   -- W(0, 1, 2)
  | 10 => (-1 : ℚ)   -- W(1, 3)
  | 11 => (1 : ℚ)   -- W(0, 1, 3)
  | 12 => (-1 : ℚ)   -- W(2, 3)
  | 13 => (1 : ℚ)   -- W(0, 2, 3)
  | 14 => (1 : ℚ)   -- W(1, 2, 3)
  | 15 => (-2 : ℚ)   -- W(0, 1, 2, 3)
  | 19 => (1 : ℚ)   -- W(0, 1, 4)
  | 22 => (1 : ℚ)   -- W(1, 2, 4)
  | 23 => (-1 : ℚ)   -- W(0, 1, 2, 4)
  | 24 => (22 : ℚ)   -- W(3, 4)
  | 25 => (-22 : ℚ)   -- W(0, 3, 4)
  | 26 => (-22 : ℚ)   -- W(1, 3, 4)
  | 27 => (22 : ℚ)   -- W(0, 1, 3, 4)
  | 28 => (-22 : ℚ)   -- W(2, 3, 4)
  | 29 => (22 : ℚ)   -- W(0, 2, 3, 4)
  | 30 => (21 : ℚ)   -- W(1, 2, 3, 4)
  | 31 => (-21 : ℚ)   -- W(0, 1, 2, 3, 4)
  | 33 => (-23 : ℚ)   -- W(0, 5)
  | 34 => (-23 : ℚ)   -- W(1, 5)
  | 35 => (23 : ℚ)   -- W(0, 1, 5)
  | 36 => (-23 : ℚ)   -- W(2, 5)
  | 37 => (23 : ℚ)   -- W(0, 2, 5)
  | 38 => (24 : ℚ)   -- W(1, 2, 5)
  | 39 => (-25 : ℚ)   -- W(0, 1, 2, 5)
  | 41 => (1 : ℚ)   -- W(0, 3, 5)
  | 42 => (1 : ℚ)   -- W(1, 3, 5)
  | 43 => (21 : ℚ)   -- W(0, 1, 3, 5)
  | 44 => (1 : ℚ)   -- W(2, 3, 5)
  | 45 => (21 : ℚ)   -- W(0, 2, 3, 5)
  | 46 => (19 : ℚ)   -- W(1, 2, 3, 5)
  | 47 => (-41 : ℚ)   -- W(0, 1, 2, 3, 5)
  | 49 => (1 : ℚ)   -- W(0, 4, 5)
  | 51 => (21 : ℚ)   -- W(0, 1, 4, 5)
  | 52 => (1 : ℚ)   -- W(2, 4, 5)
  | 53 => (22 : ℚ)   -- W(0, 2, 4, 5)
  | 54 => (20 : ℚ)   -- W(1, 2, 4, 5)
  | 55 => (-42 : ℚ)   -- W(0, 1, 2, 4, 5)
  | 56 => (-23 : ℚ)   -- W(3, 4, 5)
  | 57 => (44 : ℚ)   -- W(0, 3, 4, 5)
  | 58 => (22 : ℚ)   -- W(1, 3, 4, 5)
  | 59 => (-65 : ℚ)   -- W(0, 1, 3, 4, 5)
  | 60 => (44 : ℚ)   -- W(2, 3, 4, 5)
  | 61 => (-88 : ℚ)   -- W(0, 2, 3, 4, 5)
  | 62 => (-64 : ℚ)   -- W(1, 2, 3, 4, 5)
  | 63 => (108 : ℚ)   -- W(0, 1, 2, 3, 4, 5)
  | _ => 0

/-- The real-valued core is DEFINED as the cast of the rational one, so the
bridge between the two is `rfl`.  Every finite check downstream runs in `ℚ`,
where `≤` is decidable; `ℝ` has no decision procedure and a 729-point or
64-subset enumeration there is simply not available. -/
noncomputable def witnessCore (n : ℕ) : ℝ := ((witnessCoreQ n : ℚ) : ℝ)

/-- The rational tensor core, indexed by subset. -/
def witnessWQ (S : Finset (Fin 6)) : ℚ := witnessCoreQ (subsetMask S)

noncomputable def witnessW (S : Finset (Fin 6)) : ℝ := witnessCore (subsetMask S)

theorem witnessW_eq_cast (S : Finset (Fin 6)) :
    witnessW S = ((witnessWQ S : ℚ) : ℝ) := rfl

/-- The witness world. -/
noncomputable def witnessWorld : (Fin 6 → Fin 3) → ℝ :=
  scalarMultiaffineWorld witnessG witnessB witnessPhi witnessW

theorem cornerQ6_nonnegative (i : Fin 6) (u : Fin 3) : 0 ≤ cornerQ6 i u := by
  unfold cornerQ6
  by_cases h : u = 0 <;> simp [h]

theorem cornerQ6_normalized :
    ∑ c : Fin 6 → Fin 3, jointWeight cornerQ6 c = 1 := by
  classical
  have hterm : ∀ c : Fin 6 → Fin 3,
      jointWeight cornerQ6 c = if c = (fun _ => 0) then 1 else 0 := by
    intro c
    unfold jointWeight cornerQ6
    by_cases h : c = (fun _ => 0)
    · subst h
      simp
    · have : ∃ j, c j ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact h (funext fun j => hcon j)
      obtain ⟨j, hj⟩ := this
      rw [if_neg h]
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      simp [hj]
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  simp

/-- Rank one at every coordinate, for free: the witness is in normal form. -/
theorem witnessWorld_allCoordinatesRankOne :
    AllCoordinatesInteractionContrastRankOne cornerQ6 witnessWorld :=
  scalarMultiaffineWorld_allCoordinatesInteractionContrastRankOne
    cornerQ6 cornerQ6_normalized witnessG witnessB witnessPhi witnessW

theorem witnessWorld_rankOne_at (i : Fin 6) (u0 : Fin 3) :
    InteractionContrastRankOne cornerQ6 witnessWorld i u0 :=
  scalarMultiaffineWorld_interactionContrastRankOne
    cornerQ6 cornerQ6_normalized witnessG witnessB witnessPhi witnessW i u0

/-- `witnessPhi` takes only two values: every action's latent value equals that
of action `1` or that of action `0`.  This is what makes the witness a
TWO-PROFILE world, and it is why the coefficient pattern is `(0,1,0)`. -/
theorem witnessPhi_two_valued (i : Fin 6) (u : Fin 3) :
    witnessPhi i u = witnessPhi i 1 ∨ witnessPhi i u = witnessPhi i 0 := by
  unfold witnessPhi
  by_cases h : u = 1
  · exact Or.inl (by simp [h])
  · exact Or.inr (by simp [h])

/-- At most two interaction profiles at every coordinate, algebraically: actions
sharing a latent value share their whole centred profile, and `witnessPhi` has
only two values.  No minor is enumerated. -/
theorem witnessWorld_atMostTwoProfiles (i : Fin 6) (u0 : Fin 3) :
    HasAtMostTwoInteractionProfiles cornerQ6 witnessWorld i u0 := by
  classical
  refine ⟨1, 0, ?_⟩
  intro u
  rcases witnessPhi_two_valued i u with hu | hu
  · left
    intro z
    exact scalarMultiaffineWorld_profile_eq_of_phi_eq cornerQ6 cornerQ6_normalized
      witnessG witnessB witnessPhi witnessW i u0 u 1 hu z
  · right
    intro z
    exact scalarMultiaffineWorld_profile_eq_of_phi_eq cornerQ6 cornerQ6_normalized
      witnessG witnessB witnessPhi witnessW i u0 u 0 hu z

/-- Every coordinate of the witness satisfies the exact minor constraints that the
raw-world search writes, so the computational search class and the formal class
agree on this world. -/
theorem witnessWorld_allMinorsZero (i : Fin 6) (u0 : Fin 3) :
    AllInteractionContrastProfileMinorsZero cornerQ6 witnessWorld i u0 :=
  scalarMultiaffineWorld_allMinorsZero cornerQ6 cornerQ6_normalized
    witnessG witnessB witnessPhi witnessW i u0

end CIGAMF.P13.D6StrictRankOneM6Witness
