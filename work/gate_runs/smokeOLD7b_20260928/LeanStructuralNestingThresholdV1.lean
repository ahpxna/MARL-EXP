import Mathlib
import «LeanStructuralGeometryWitnessesV4»
import «LeanStructuralPrefixCoverDimensionV1»

/-!
# The exact nesting tolerance of a structural instance, and three exact witnesses

For a finite instance `f : ι → Ω → ℝ` write

* `selectedRadius f S = supportOsc Sᶜ f / 2`  (the repo's structural loss), and
* `normalizedRadius f S = supportOsc Sᶜ f / modularSpan univ f`
  (the same loss divided by the total component span `D`).

`OnePrefixChain (objective) e` says ONE full ranking has, at EVERY budget `k`,
its first `k` components within `e` of the best `k`-subset.  The exact nesting
tolerance of an instance is the least `e` for which this holds:

    NestingThreshold f t  :=  (∀ e < t, ¬ OnePrefixChain (selectedRadius f) e)
                              ∧ OnePrefixChain (selectedRadius f) t .

`epsilon_nest(f)` is the same number for `normalizedRadius`, i.e. `2 t / D`.

This file proves three EXACT thresholds:

* `nest_threshold`   : the 4-component, 3-scenario matrix
  `[[0,1,0],[1,0,1],[1,0,0],[0,0,1]]` has `t = 1/2`, i.e. `epsilon_nest = 1/4`
  (`D = 4`).  This is the previously recorded lower witness.
* `dead_threshold`   : the 3-component, 2-scenario matrix `[[0,-1],[0,0],[0,1]]`
  has `t = 1/2`, i.e. `epsilon_nest = 1/2` (`D = 2`).  **This refutes
  `epsilon_nest^star = 1/4`.**  One of its components is constant.
* `gap_threshold c`  : for every real `c ≥ 1` the 3-component, 2-scenario matrix
  `[[0,-c],[0,1],[0,c]]` — every component NON-constant — has `t = (c-1)/2`,
  i.e. `epsilon_nest = (c-1)/(2c+1)`, which tends to `1/2` from below.
  So `epsilon_nest^star ≥ 1/2` even with all components non-constant, and
  `1/2` is not attained inside that subfamily.

## WHAT THIS DOES NOT ESTABLISH

* It does NOT prove any universal upper bound on `epsilon_nest`.  In particular
  `epsilon_nest^star ≤ 1/2` is NOT proved here and is NOT known.  The only
  compiled universal upper bound in this repository is the per-layer `2/3`
  estimate of `LeanStructuralRecourseUniformNestingV1`, which bounds one budget
  layer against one competitor and does not by itself produce a ranking.
* It does NOT prove `epsilon_nest^star = 1/2`.  Three instances are exhibited;
  `sup` over all instances is bounded BELOW by `1/2`, never above.
* It says nothing about the DP recurrence
  `H(S) = max {g(S), min_{i ∈ S} H(S \ {i})}`.  That recurrence is only
  cross-checked numerically (probe `scripts/C1_structural_eps_nest_dp.py`,
  exhaustive permutation comparison for every m ≤ 8); it is NOT formalized.
* `NestingThreshold` quantifies over rankings of the given instance only.  No
  statement is made about menus of more than one ranking, about randomized
  rankings, or about any computational question.
* The instances here are exact rational (resp. one-real-parameter) matrices.
  Nothing is claimed for infinite `Ω`, infinite `ι`, or `D = 0`.
-/

namespace CIGAMF.P13.StructuralNestingThreshold

open Finset
open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.StructuralRankability
open CIGAMF.V4.StructuralGeometryWitnesses
open CIGAMF.P13.StructuralPrefixCoverDimension

noncomputable section

section General

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]

/-- Residual oscillation of the unselected components, normalized by the total
component span `D = modularSpan univ f`. -/
def normalizedRadius (f : ι → Ω → ℝ) (S : Finset ι) : ℝ :=
  supportOsc Sᶜ f / modularSpan Finset.univ f

theorem selectedRadius_nonneg (f : ι → Ω → ℝ) (S : Finset ι) :
    0 ≤ selectedRadius f S := by
  have := osc_nonneg (sumComponent Sᶜ f)
  simp only [selectedRadius, supportOsc]
  linarith

theorem normalizedRadius_eq_selectedRadius_div
    (f : ι → Ω → ℝ) (S : Finset ι) :
    normalizedRadius f S = selectedRadius f S / (modularSpan Finset.univ f / 2) := by
  simp only [normalizedRadius, selectedRadius]
  rcases eq_or_ne (modularSpan Finset.univ f) 0 with h | h
  · simp [h]
  · field_simp

/-- The exact nesting tolerance of `f` on the structural loss `selectedRadius`. -/
def NestingThreshold (f : ι → Ω → ℝ) (t : ℝ) : Prop :=
  (∀ e : ℝ, e < t → ¬ OnePrefixChain (selectedRadius f) e) ∧
    OnePrefixChain (selectedRadius f) t

/-- The same number for the normalized loss `normalizedRadius = selectedRadius / (D/2)`. -/
def NormalizedNestingThreshold (f : ι → Ω → ℝ) (t : ℝ) : Prop :=
  (∀ e : ℝ, e < t → ¬ OnePrefixChain (normalizedRadius f) e) ∧
    OnePrefixChain (normalizedRadius f) t

theorem scale_ineq (a b c e : ℝ) (hc : 0 < c) :
    a / c ≤ b / c + e ↔ a ≤ b + c * e := by
  rw [div_le_iff₀ hc]
  have h : (b / c + e) * c = b + c * e := by field_simp
  rw [h]

theorem epsilonOptimalAt_div {I : Type*} [Fintype I] [DecidableEq I]
    (obj : Finset I → ℝ) (c e : ℝ) (hc : 0 < c) (k : ℕ) (S : Finset I) :
    EpsilonOptimalAt (fun T => obj T / c) e k S ↔ EpsilonOptimalAt obj (c * e) k S := by
  constructor
  · rintro ⟨hcard, h⟩
    refine ⟨hcard, fun T hT => ?_⟩
    have := h T hT
    exact (scale_ineq (obj S) (obj T) c e hc).1 this
  · rintro ⟨hcard, h⟩
    refine ⟨hcard, fun T hT => ?_⟩
    have := h T hT
    exact (scale_ineq (obj S) (obj T) c e hc).2 this

/-- Transfer an exact threshold from the structural loss to the normalized loss. -/
theorem normalized_threshold_of_selected
    (f : ι → Ω → ℝ) (D t : ℝ) (hD : 0 < D)
    (hspan : modularSpan Finset.univ f = D)
    (h : NestingThreshold f t) :
    NormalizedNestingThreshold f (2 * t / D) := by
  have hc : (0:ℝ) < D / 2 := by linarith
  have hfun : normalizedRadius f = fun S => selectedRadius f S / (D / 2) := by
    funext S
    rw [normalizedRadius_eq_selectedRadius_div, hspan]
  constructor
  · rintro e he ⟨ranking, hfull, hopt⟩
    have hlt : D / 2 * e < t := by
      rw [lt_div_iff₀ hD] at he
      linarith
    refine h.1 (D / 2 * e) hlt ⟨ranking, hfull, fun k hk => ?_⟩
    have hkk := hopt k hk
    rw [hfun] at hkk
    exact (epsilonOptimalAt_div (selectedRadius f) (D / 2) e hc k _).1 hkk
  · obtain ⟨ranking, hfull, hopt⟩ := h.2
    refine ⟨ranking, hfull, fun k hk => ?_⟩
    rw [hfun]
    refine (epsilonOptimalAt_div (selectedRadius f) (D / 2) (2 * t / D) hc k _).2 ?_
    have hcancel : D / 2 * (2 * t / D) = t := by field_simp
    rw [hcancel]
    exact hopt k hk

end General

/-! ## Complement tables -/

@[simp] theorem fin4_compl_empty : (∅ : Finset (Fin 4))ᶜ = Finset.univ := by decide
@[simp] theorem fin4_compl_univ : (Finset.univ : Finset (Fin 4))ᶜ = ∅ := by decide
@[simp] theorem fin4_compl_0 : ({0} : Finset (Fin 4))ᶜ = {1,2,3} := by decide
@[simp] theorem fin4_compl_1 : ({1} : Finset (Fin 4))ᶜ = {0,2,3} := by decide
@[simp] theorem fin4_compl_2 : ({2} : Finset (Fin 4))ᶜ = {0,1,3} := by decide
@[simp] theorem fin4_compl_3 : ({3} : Finset (Fin 4))ᶜ = {0,1,2} := by decide
@[simp] theorem fin4_compl_01 : ({0,1} : Finset (Fin 4))ᶜ = {2,3} := by decide
@[simp] theorem fin4_compl_02 : ({0,2} : Finset (Fin 4))ᶜ = {1,3} := by decide
@[simp] theorem fin4_compl_03 : ({0,3} : Finset (Fin 4))ᶜ = {1,2} := by decide
@[simp] theorem fin4_compl_12 : ({1,2} : Finset (Fin 4))ᶜ = {0,3} := by decide
@[simp] theorem fin4_compl_13 : ({1,3} : Finset (Fin 4))ᶜ = {0,2} := by decide
@[simp] theorem fin4_compl_23 : ({2,3} : Finset (Fin 4))ᶜ = {0,1} := by decide
@[simp] theorem fin4_compl_012 : ({0,1,2} : Finset (Fin 4))ᶜ = {3} := by decide

@[simp] theorem fin3_compl_empty : (∅ : Finset (Fin 3))ᶜ = Finset.univ := by decide
@[simp] theorem fin3_compl_univ : (Finset.univ : Finset (Fin 3))ᶜ = ∅ := by decide

theorem fin4_card_one : ∀ S : Finset (Fin 4), S.card = 1 →
    S = {0} ∨ S = {1} ∨ S = {2} ∨ S = {3} := by decide

theorem fin4_card_two : ∀ S : Finset (Fin 4), S.card = 2 →
    S = {0,1} ∨ S = {0,2} ∨ S = {0,3} ∨ S = {1,2} ∨ S = {1,3} ∨ S = {2,3} := by decide

theorem fin3_card_one : ∀ S : Finset (Fin 3), S.card = 1 →
    S = {0} ∨ S = {1} ∨ S = {2} := by decide

theorem fin3_card_two : ∀ S : Finset (Fin 3), S.card = 2 →
    S = {0,1} ∨ S = {0,2} ∨ S = {1,2} := by decide

/-! ## Witness 1: the 4 x 3 matrix with epsilon_nest = 1/4 exactly -/

/-- Rows `[0,1,0]`, `[1,0,1]`, `[1,0,0]`, `[0,0,1]`. -/
def nestF : Fin 4 → Fin 3 → ℝ := fun j a =>
  match j, a with
  | 0, 1 => 1
  | 1, 0 => 1
  | 1, 2 => 1
  | 2, 0 => 1
  | 3, 2 => 1
  | _, _ => 0

theorem nest_r_empty : selectedRadius nestF (∅ : Finset (Fin 4)) = 1 / 2 := by
  calc _ = (2 - 1 : ℝ) / 2 := selectedRadius_from_extrema nestF ∅ 2 1
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) 0 1
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
    _ = 1 / 2 := by norm_num

theorem nest_r0 : selectedRadius nestF ({0} : Finset (Fin 4)) = 1 := by
  calc _ = (2 - 0 : ℝ) / 2 := selectedRadius_from_extrema nestF {0} 2 0
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) 0 1
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
    _ = 1 := by norm_num

theorem nest_r1 : selectedRadius nestF ({1} : Finset (Fin 4)) = 0 := by
  calc _ = (1 - 1 : ℝ) / 2 := selectedRadius_from_extrema nestF {1} 1 1
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) 0 0
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
    _ = 0 := by norm_num

theorem nest_r2 : selectedRadius nestF ({2} : Finset (Fin 4)) = 1 / 2 := by
  calc _ = (2 - 1 : ℝ) / 2 := selectedRadius_from_extrema nestF {2} 2 1
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) 2 0
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
    _ = 1 / 2 := by norm_num

theorem nest_r3 : selectedRadius nestF ({3} : Finset (Fin 4)) = 1 / 2 := by
  calc _ = (2 - 1 : ℝ) / 2 := selectedRadius_from_extrema nestF {3} 2 1
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) 0 1
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
    _ = 1 / 2 := by norm_num

theorem nest_r01 : selectedRadius nestF ({0,1} : Finset (Fin 4)) = 1 / 2 := by
  calc _ = (1 - 0 : ℝ) / 2 := selectedRadius_from_extrema nestF {0,1} 1 0
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) 0 1
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
    _ = 1 / 2 := by norm_num

theorem nest_r02 : selectedRadius nestF ({0,2} : Finset (Fin 4)) = 1 := by
  calc _ = (2 - 0 : ℝ) / 2 := selectedRadius_from_extrema nestF {0,2} 2 0
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) 2 1
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
    _ = 1 := by norm_num

theorem nest_r03 : selectedRadius nestF ({0,3} : Finset (Fin 4)) = 1 := by
  calc _ = (2 - 0 : ℝ) / 2 := selectedRadius_from_extrema nestF {0,3} 2 0
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) 0 1
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
    _ = 1 := by norm_num

theorem nest_r12 : selectedRadius nestF ({1,2} : Finset (Fin 4)) = 1 / 2 := by
  calc _ = (1 - 0 : ℝ) / 2 := selectedRadius_from_extrema nestF {1,2} 1 0
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) 1 0
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
    _ = 1 / 2 := by norm_num

theorem nest_r13 : selectedRadius nestF ({1,3} : Finset (Fin 4)) = 1 / 2 := by
  calc _ = (1 - 0 : ℝ) / 2 := selectedRadius_from_extrema nestF {1,3} 1 0
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) 0 2
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
    _ = 1 / 2 := by norm_num

theorem nest_r23 : selectedRadius nestF ({2,3} : Finset (Fin 4)) = 0 := by
  calc _ = (1 - 1 : ℝ) / 2 := selectedRadius_from_extrema nestF {2,3} 1 1
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) 0 0
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
    _ = 0 := by norm_num

theorem nest_r012 : selectedRadius nestF ({0,1,2} : Finset (Fin 4)) = 1 / 2 := by
  calc _ = (1 - 0 : ℝ) / 2 := selectedRadius_from_extrema nestF {0,1,2} 1 0
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) 2 0
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
    _ = 1 / 2 := by norm_num

theorem nest_runiv : selectedRadius nestF (Finset.univ : Finset (Fin 4)) = 0 := by
  calc _ = (0 - 0 : ℝ) / 2 := selectedRadius_from_extrema nestF Finset.univ 0 0
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) 0 0
        (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num) (by simp [sumComponent, nestF, Fin.sum_univ_four] <;> norm_num)
    _ = 0 := by norm_num

def nestRanking : List (Fin 4) := [1, 0, 2, 3]

theorem nest_full : IsFullRanking nestRanking := by
  constructor
  · decide
  · ext x; fin_cases x <;> simp [nestRanking]

theorem nest_prefix0 : prefixSet nestRanking 0 = (∅ : Finset (Fin 4)) := by decide
theorem nest_prefix1 : prefixSet nestRanking 1 = ({1} : Finset (Fin 4)) := by decide
theorem nest_prefix2 : prefixSet nestRanking 2 = ({0,1} : Finset (Fin 4)) := by decide
theorem nest_prefix3 : prefixSet nestRanking 3 = ({0,1,2} : Finset (Fin 4)) := by decide
theorem nest_prefix4 : prefixSet nestRanking 4 = (Finset.univ : Finset (Fin 4)) := by decide

/-- Upper half: the ranking `[1,0,2,3]` is `1/2`-good at every budget. -/
theorem nest_chain_half : OnePrefixChain (selectedRadius nestF) (1 / 2) := by
  refine ⟨nestRanking, nest_full, ?_⟩
  intro k hk
  simp only [Fintype.card_fin] at hk
  have hbase : ∀ T : Finset (Fin 4), 0 ≤ selectedRadius nestF T :=
    fun T => selectedRadius_nonneg nestF T
  interval_cases k
  · refine ⟨by rw [nest_prefix0]; decide, fun T hT => ?_⟩
    rw [nest_prefix0, nest_r_empty]; have := hbase T; linarith
  · refine ⟨by rw [nest_prefix1]; decide, fun T hT => ?_⟩
    rw [nest_prefix1, nest_r1]; have := hbase T; linarith
  · refine ⟨by rw [nest_prefix2]; decide, fun T hT => ?_⟩
    rw [nest_prefix2, nest_r01]; have := hbase T; linarith
  · refine ⟨by rw [nest_prefix3]; decide, fun T hT => ?_⟩
    rw [nest_prefix3, nest_r012]; have := hbase T; linarith
  · refine ⟨by rw [nest_prefix4]; decide, fun T hT => ?_⟩
    rw [nest_prefix4, nest_runiv]; have := hbase T; linarith

/-- Lower half: below `1/2` no single ranking works. -/
theorem nest_no_chain_below_half (e : ℝ) (he : e < 1 / 2) :
    ¬ OnePrefixChain (selectedRadius nestF) e := by
  rintro ⟨ranking, hfull, hopt⟩
  have hc1 := CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full
    ranking hfull 1 (by simp)
  have hc2 := CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full
    ranking hfull 2 (by simp)
  have h1 := (hopt 1 (by simp)).2 ({1} : Finset (Fin 4)) (by decide)
  have h2 := (hopt 2 (by simp)).2 ({2,3} : Finset (Fin 4)) (by decide)
  rw [nest_r1] at h1
  rw [nest_r23] at h2
  have hp1 : prefixSet ranking 1 = ({1} : Finset (Fin 4)) := by
    rcases fin4_card_one _ hc1 with h | h | h | h
    · exfalso; rw [h, nest_r0] at h1; linarith
    · exact h
    · exfalso; rw [h, nest_r2] at h1; linarith
    · exfalso; rw [h, nest_r3] at h1; linarith
  have hp2 : prefixSet ranking 2 = ({2,3} : Finset (Fin 4)) := by
    rcases fin4_card_two _ hc2 with h | h | h | h | h | h
    · exfalso; rw [h, nest_r01] at h2; linarith
    · exfalso; rw [h, nest_r02] at h2; linarith
    · exfalso; rw [h, nest_r03] at h2; linarith
    · exfalso; rw [h, nest_r12] at h2; linarith
    · exfalso; rw [h, nest_r13] at h2; linarith
    · exact h
  have hnested := prefixSet_nested ranking 1
  rw [hp1, hp2] at hnested
  have hmem := hnested (by decide : (1 : Fin 4) ∈ ({1} : Finset (Fin 4)))
  exact absurd hmem (by decide)

theorem nest_threshold : NestingThreshold nestF (1 / 2) :=
  ⟨nest_no_chain_below_half, nest_chain_half⟩

theorem nest_modularSpan : modularSpan Finset.univ nestF = 4 := by
  have h0 : componentSpan nestF 0 = 1 := by
    calc _ = (1 - 0 : ℝ) := componentSpan_from_extrema nestF 0 1 0
          (by intro a; fin_cases a <;> simp [nestF] <;> norm_num)
          (by intro a; fin_cases a <;> simp [nestF] <;> norm_num) 1 0
          (by simp [nestF] <;> norm_num) (by simp [nestF] <;> norm_num)
      _ = 1 := by norm_num
  have h1 : componentSpan nestF 1 = 1 := by
    calc _ = (1 - 0 : ℝ) := componentSpan_from_extrema nestF 1 1 0
          (by intro a; fin_cases a <;> simp [nestF] <;> norm_num)
          (by intro a; fin_cases a <;> simp [nestF] <;> norm_num) 0 1
          (by simp [nestF] <;> norm_num) (by simp [nestF] <;> norm_num)
      _ = 1 := by norm_num
  have h2 : componentSpan nestF 2 = 1 := by
    calc _ = (1 - 0 : ℝ) := componentSpan_from_extrema nestF 2 1 0
          (by intro a; fin_cases a <;> simp [nestF] <;> norm_num)
          (by intro a; fin_cases a <;> simp [nestF] <;> norm_num) 0 1
          (by simp [nestF] <;> norm_num) (by simp [nestF] <;> norm_num)
      _ = 1 := by norm_num
  have h3 : componentSpan nestF 3 = 1 := by
    calc _ = (1 - 0 : ℝ) := componentSpan_from_extrema nestF 3 1 0
          (by intro a; fin_cases a <;> simp [nestF] <;> norm_num)
          (by intro a; fin_cases a <;> simp [nestF] <;> norm_num) 2 0
          (by simp [nestF] <;> norm_num) (by simp [nestF] <;> norm_num)
      _ = 1 := by norm_num
  simp only [modularSpan, Fin.sum_univ_four, h0, h1, h2, h3]
  norm_num

/-- `epsilon_nest` of the 4 x 3 witness is EXACTLY `1/4`. -/
theorem nest_normalized_threshold : NormalizedNestingThreshold nestF (1 / 4) := by
  have h := normalized_threshold_of_selected nestF 4 (1/2) (by norm_num)
    nest_modularSpan nest_threshold
  have hEq : 2 * (1/2 : ℝ) / 4 = 1 / 4 := by norm_num
  rwa [hEq] at h

/-! ## Witness 2: a 3 x 2 instance with epsilon_nest = 1/2 exactly -/

/-- Rows `[0,-1]`, `[0,0]`, `[0,1]`.  The middle component is constant. -/
def deadF : Fin 3 → Fin 2 → ℝ := fun j a =>
  match j, a with
  | 0, 1 => -1
  | 2, 1 => 1
  | _, _ => 0

theorem dead_r_empty : selectedRadius deadF (∅ : Finset (Fin 3)) = 0 := by
  calc _ = (0 - 0 : ℝ) / 2 := selectedRadius_from_extrema deadF ∅ 0 0
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) 0 0
        (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
    _ = 0 := by norm_num

theorem dead_r0 : selectedRadius deadF ({0} : Finset (Fin 3)) = 1 / 2 := by
  calc _ = (1 - 0 : ℝ) / 2 := selectedRadius_from_extrema deadF {0} 1 0
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) 1 0
        (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
    _ = 1 / 2 := by norm_num

theorem dead_r1 : selectedRadius deadF ({1} : Finset (Fin 3)) = 0 := by
  calc _ = (0 - 0 : ℝ) / 2 := selectedRadius_from_extrema deadF {1} 0 0
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) 0 0
        (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
    _ = 0 := by norm_num

theorem dead_r2 : selectedRadius deadF ({2} : Finset (Fin 3)) = 1 / 2 := by
  calc _ = (0 - (-1) : ℝ) / 2 := selectedRadius_from_extrema deadF {2} 0 (-1)
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) 0 1
        (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
    _ = 1 / 2 := by norm_num

theorem dead_r01 : selectedRadius deadF ({0,1} : Finset (Fin 3)) = 1 / 2 := by
  calc _ = (1 - 0 : ℝ) / 2 := selectedRadius_from_extrema deadF {0,1} 1 0
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) 1 0
        (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
    _ = 1 / 2 := by norm_num

theorem dead_r02 : selectedRadius deadF ({0,2} : Finset (Fin 3)) = 0 := by
  calc _ = (0 - 0 : ℝ) / 2 := selectedRadius_from_extrema deadF {0,2} 0 0
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) 0 0
        (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
    _ = 0 := by norm_num

theorem dead_r12 : selectedRadius deadF ({1,2} : Finset (Fin 3)) = 1 / 2 := by
  calc _ = (0 - (-1) : ℝ) / 2 := selectedRadius_from_extrema deadF {1,2} 0 (-1)
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) 0 1
        (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
    _ = 1 / 2 := by norm_num

theorem dead_runiv : selectedRadius deadF (Finset.univ : Finset (Fin 3)) = 0 := by
  calc _ = (0 - 0 : ℝ) / 2 := selectedRadius_from_extrema deadF Finset.univ 0 0
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
        (by intro a; fin_cases a <;> simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) 0 0
        (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num) (by simp [sumComponent, deadF, Fin.sum_univ_three] <;> norm_num)
    _ = 0 := by norm_num

def deadRanking : List (Fin 3) := [1, 2, 0]

theorem dead_full : IsFullRanking deadRanking := by
  constructor
  · decide
  · ext x; fin_cases x <;> simp [deadRanking]

theorem dead_prefix0 : prefixSet deadRanking 0 = (∅ : Finset (Fin 3)) := by decide
theorem dead_prefix1 : prefixSet deadRanking 1 = ({1} : Finset (Fin 3)) := by decide
theorem dead_prefix2 : prefixSet deadRanking 2 = ({1,2} : Finset (Fin 3)) := by decide
theorem dead_prefix3 : prefixSet deadRanking 3 = (Finset.univ : Finset (Fin 3)) := by decide

theorem dead_chain_half : OnePrefixChain (selectedRadius deadF) (1 / 2) := by
  refine ⟨deadRanking, dead_full, ?_⟩
  intro k hk
  simp only [Fintype.card_fin] at hk
  have hbase : ∀ T : Finset (Fin 3), 0 ≤ selectedRadius deadF T :=
    fun T => selectedRadius_nonneg deadF T
  interval_cases k
  · refine ⟨by rw [dead_prefix0]; decide, fun T hT => ?_⟩
    rw [dead_prefix0, dead_r_empty]; have := hbase T; linarith
  · refine ⟨by rw [dead_prefix1]; decide, fun T hT => ?_⟩
    rw [dead_prefix1, dead_r1]; have := hbase T; linarith
  · refine ⟨by rw [dead_prefix2]; decide, fun T hT => ?_⟩
    rw [dead_prefix2, dead_r12]; have := hbase T; linarith
  · refine ⟨by rw [dead_prefix3]; decide, fun T hT => ?_⟩
    rw [dead_prefix3, dead_runiv]; have := hbase T; linarith

theorem dead_no_chain_below_half (e : ℝ) (he : e < 1 / 2) :
    ¬ OnePrefixChain (selectedRadius deadF) e := by
  rintro ⟨ranking, hfull, hopt⟩
  have hc1 := CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full
    ranking hfull 1 (by simp)
  have hc2 := CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full
    ranking hfull 2 (by simp)
  have h1 := (hopt 1 (by simp)).2 ({1} : Finset (Fin 3)) (by decide)
  have h2 := (hopt 2 (by simp)).2 ({0,2} : Finset (Fin 3)) (by decide)
  rw [dead_r1] at h1
  rw [dead_r02] at h2
  have hp1 : prefixSet ranking 1 = ({1} : Finset (Fin 3)) := by
    rcases fin3_card_one _ hc1 with h | h | h
    · exfalso; rw [h, dead_r0] at h1; linarith
    · exact h
    · exfalso; rw [h, dead_r2] at h1; linarith
  have hp2 : prefixSet ranking 2 = ({0,2} : Finset (Fin 3)) := by
    rcases fin3_card_two _ hc2 with h | h | h
    · exfalso; rw [h, dead_r01] at h2; linarith
    · exact h
    · exfalso; rw [h, dead_r12] at h2; linarith
  have hnested := prefixSet_nested ranking 1
  rw [hp1, hp2] at hnested
  have hmem := hnested (by decide : (1 : Fin 3) ∈ ({1} : Finset (Fin 3)))
  exact absurd hmem (by decide)

theorem dead_threshold : NestingThreshold deadF (1 / 2) :=
  ⟨dead_no_chain_below_half, dead_chain_half⟩

theorem dead_modularSpan : modularSpan Finset.univ deadF = 2 := by
  have h0 : componentSpan deadF 0 = 1 := by
    calc _ = (0 - (-1) : ℝ) := componentSpan_from_extrema deadF 0 0 (-1)
          (by intro a; fin_cases a <;> simp [deadF] <;> norm_num)
          (by intro a; fin_cases a <;> simp [deadF] <;> norm_num) 0 1
          (by simp [deadF] <;> norm_num) (by simp [deadF] <;> norm_num)
      _ = 1 := by norm_num
  have h1 : componentSpan deadF 1 = 0 := by
    calc _ = (0 - 0 : ℝ) := componentSpan_from_extrema deadF 1 0 0
          (by intro a; fin_cases a <;> simp [deadF])
          (by intro a; fin_cases a <;> simp [deadF]) 0 0
          (by simp [deadF] <;> norm_num) (by simp [deadF] <;> norm_num)
      _ = 0 := by norm_num
  have h2 : componentSpan deadF 2 = 1 := by
    calc _ = (1 - 0 : ℝ) := componentSpan_from_extrema deadF 2 1 0
          (by intro a; fin_cases a <;> simp [deadF] <;> norm_num)
          (by intro a; fin_cases a <;> simp [deadF] <;> norm_num) 1 0
          (by simp [deadF] <;> norm_num) (by simp [deadF] <;> norm_num)
      _ = 1 := by norm_num
  simp only [modularSpan, Fin.sum_univ_three, h0, h1, h2]
  norm_num

/-- **Refutation of `epsilon_nest^star = 1/4`.**  `epsilon_nest (deadF) = 1/2`. -/
theorem dead_normalized_threshold : NormalizedNestingThreshold deadF (1 / 2) := by
  have h := normalized_threshold_of_selected deadF 2 (1/2) (by norm_num)
    dead_modularSpan dead_threshold
  have hEq : 2 * (1/2 : ℝ) / 2 = 1 / 2 := by norm_num
  rwa [hEq] at h

/-! ## Witness 3: a one-parameter family of NON-degenerate instances -/

/-- Rows `[0,-c]`, `[0,1]`, `[0,c]`.  For `c ≥ 1` all three components have
non-zero span (`c`, `1`, `c`), so no component is constant. -/
def gapF (c : ℝ) : Fin 3 → Fin 2 → ℝ := fun j a =>
  match j, a with
  | 0, 1 => -c
  | 1, 1 => 1
  | 2, 1 => c
  | _, _ => 0

variable {c : ℝ}

theorem gap_r_empty (hc : 1 ≤ c) : selectedRadius (gapF c) (∅ : Finset (Fin 3)) = 1 / 2 := by
  calc _ = (1 - 0 : ℝ) / 2 := selectedRadius_from_extrema (gapF c) ∅ 1 0
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) 1 0
        (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
    _ = 1 / 2 := by norm_num

theorem gap_r0 (hc : 1 ≤ c) :
    selectedRadius (gapF c) ({0} : Finset (Fin 3)) = (c + 1) / 2 := by
  calc _ = ((c + 1) - 0 : ℝ) / 2 := selectedRadius_from_extrema (gapF c) {0} (c + 1) 0
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) 1 0
        (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
    _ = (c + 1) / 2 := by norm_num

theorem gap_r1 (hc : 1 ≤ c) : selectedRadius (gapF c) ({1} : Finset (Fin 3)) = 0 := by
  calc _ = (0 - 0 : ℝ) / 2 := selectedRadius_from_extrema (gapF c) {1} 0 0
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) 0 0
        (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
    _ = 0 := by norm_num

theorem gap_r2 (hc : 1 ≤ c) :
    selectedRadius (gapF c) ({2} : Finset (Fin 3)) = (c - 1) / 2 := by
  calc _ = (0 - (1 - c) : ℝ) / 2 := selectedRadius_from_extrema (gapF c) {2} 0 (1 - c)
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) 0 1
        (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
    _ = (c - 1) / 2 := by ring

theorem gap_r01 (hc : 1 ≤ c) :
    selectedRadius (gapF c) ({0,1} : Finset (Fin 3)) = c / 2 := by
  calc _ = (c - 0 : ℝ) / 2 := selectedRadius_from_extrema (gapF c) {0,1} c 0
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) 1 0
        (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
    _ = c / 2 := by norm_num

theorem gap_r02 (hc : 1 ≤ c) :
    selectedRadius (gapF c) ({0,2} : Finset (Fin 3)) = 1 / 2 := by
  calc _ = (1 - 0 : ℝ) / 2 := selectedRadius_from_extrema (gapF c) {0,2} 1 0
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) 1 0
        (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
    _ = 1 / 2 := by norm_num

theorem gap_r12 (hc : 1 ≤ c) :
    selectedRadius (gapF c) ({1,2} : Finset (Fin 3)) = c / 2 := by
  calc _ = (0 - (-c) : ℝ) / 2 := selectedRadius_from_extrema (gapF c) {1,2} 0 (-c)
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) 0 1
        (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
    _ = c / 2 := by ring

theorem gap_runiv (hc : 1 ≤ c) :
    selectedRadius (gapF c) (Finset.univ : Finset (Fin 3)) = 0 := by
  calc _ = (0 - 0 : ℝ) / 2 := selectedRadius_from_extrema (gapF c) Finset.univ 0 0
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
        (by intro a; fin_cases a <;> simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) 0 0
        (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith) (by simp [sumComponent, gapF, Fin.sum_univ_three] <;> linarith)
    _ = 0 := by norm_num

def gapRanking : List (Fin 3) := [2, 0, 1]

theorem gap_full : IsFullRanking gapRanking := by
  constructor
  · decide
  · ext x; fin_cases x <;> simp [gapRanking]

theorem gap_prefix0 : prefixSet gapRanking 0 = (∅ : Finset (Fin 3)) := by decide
theorem gap_prefix1 : prefixSet gapRanking 1 = ({2} : Finset (Fin 3)) := by decide
theorem gap_prefix2 : prefixSet gapRanking 2 = ({0,2} : Finset (Fin 3)) := by decide
theorem gap_prefix3 : prefixSet gapRanking 3 = (Finset.univ : Finset (Fin 3)) := by decide

theorem gap_chain (hc : 1 ≤ c) :
    OnePrefixChain (selectedRadius (gapF c)) ((c - 1) / 2) := by
  refine ⟨gapRanking, gap_full, ?_⟩
  intro k hk
  simp only [Fintype.card_fin] at hk
  have hbase : ∀ T : Finset (Fin 3), 0 ≤ selectedRadius (gapF c) T :=
    fun T => selectedRadius_nonneg (gapF c) T
  interval_cases k
  · refine ⟨by rw [gap_prefix0]; decide, fun T hT => ?_⟩
    have hT0 : T = (∅ : Finset (Fin 3)) := Finset.card_eq_zero.mp hT
    rw [gap_prefix0, hT0]; linarith
  · refine ⟨by rw [gap_prefix1]; decide, fun T hT => ?_⟩
    rw [gap_prefix1, gap_r2 hc]
    have := hbase T; linarith
  · refine ⟨by rw [gap_prefix2]; decide, fun T hT => ?_⟩
    rw [gap_prefix2, gap_r02 hc]
    rcases fin3_card_two _ hT with h | h | h <;> rw [h]
    · rw [gap_r01 hc]; linarith
    · rw [gap_r02 hc]; linarith
    · rw [gap_r12 hc]; linarith
  · refine ⟨by rw [gap_prefix3]; decide, fun T hT => ?_⟩
    rw [gap_prefix3, gap_runiv hc]
    have := hbase T; linarith

theorem gap_no_chain_below (hc : 1 ≤ c) (e : ℝ) (he : e < (c - 1) / 2) :
    ¬ OnePrefixChain (selectedRadius (gapF c)) e := by
  rintro ⟨ranking, hfull, hopt⟩
  have hc1 := CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full
    ranking hfull 1 (by simp)
  have hc2 := CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full
    ranking hfull 2 (by simp)
  have h1 := (hopt 1 (by simp)).2 ({1} : Finset (Fin 3)) (by decide)
  have h2 := (hopt 2 (by simp)).2 ({0,2} : Finset (Fin 3)) (by decide)
  rw [gap_r1 hc] at h1
  rw [gap_r02 hc] at h2
  have hp1 : prefixSet ranking 1 = ({1} : Finset (Fin 3)) := by
    rcases fin3_card_one _ hc1 with h | h | h
    · exfalso; rw [h, gap_r0 hc] at h1; linarith
    · exact h
    · exfalso; rw [h, gap_r2 hc] at h1; linarith
  have hp2 : prefixSet ranking 2 = ({0,2} : Finset (Fin 3)) := by
    rcases fin3_card_two _ hc2 with h | h | h
    · exfalso; rw [h, gap_r01 hc] at h2; linarith
    · exact h
    · exfalso; rw [h, gap_r12 hc] at h2; linarith
  have hnested := prefixSet_nested ranking 1
  rw [hp1, hp2] at hnested
  have hmem := hnested (by decide : (1 : Fin 3) ∈ ({1} : Finset (Fin 3)))
  exact absurd hmem (by decide)

theorem gap_threshold (hc : 1 ≤ c) : NestingThreshold (gapF c) ((c - 1) / 2) :=
  ⟨gap_no_chain_below hc, gap_chain hc⟩

theorem gap_modularSpan (hc : 1 ≤ c) :
    modularSpan Finset.univ (gapF c) = 2 * c + 1 := by
  have h0 : componentSpan (gapF c) 0 = c := by
    calc _ = (0 - (-c) : ℝ) := componentSpan_from_extrema (gapF c) 0 0 (-c)
          (by intro a; fin_cases a <;> simp [gapF] <;> linarith)
          (by intro a; fin_cases a <;> simp [gapF] <;> linarith) 0 1
          (by simp [gapF] <;> linarith) (by simp [gapF] <;> linarith)
      _ = c := by ring
  have h1 : componentSpan (gapF c) 1 = 1 := by
    calc _ = (1 - 0 : ℝ) := componentSpan_from_extrema (gapF c) 1 1 0
          (by intro a; fin_cases a <;> simp [gapF] <;> linarith)
          (by intro a; fin_cases a <;> simp [gapF] <;> linarith) 1 0
          (by simp [gapF] <;> linarith) (by simp [gapF] <;> linarith)
      _ = 1 := by norm_num
  have h2 : componentSpan (gapF c) 2 = c := by
    calc _ = (c - 0 : ℝ) := componentSpan_from_extrema (gapF c) 2 c 0
          (by intro a; fin_cases a <;> simp [gapF] <;> linarith)
          (by intro a; fin_cases a <;> simp [gapF] <;> linarith) 1 0
          (by simp [gapF] <;> linarith) (by simp [gapF] <;> linarith)
      _ = c := by norm_num
  simp only [modularSpan, Fin.sum_univ_three, h0, h1, h2]
  ring

/-- Every component of `gapF c` has non-zero span when `c ≥ 1`. -/
theorem gap_all_components_nonconstant (hc : 1 ≤ c) (j : Fin 3) :
    0 < componentSpan (gapF c) j := by
  have h0 : componentSpan (gapF c) 0 = c := by
    calc _ = (0 - (-c) : ℝ) := componentSpan_from_extrema (gapF c) 0 0 (-c)
          (by intro a; fin_cases a <;> simp [gapF] <;> linarith)
          (by intro a; fin_cases a <;> simp [gapF] <;> linarith) 0 1
          (by simp [gapF] <;> linarith) (by simp [gapF] <;> linarith)
      _ = c := by ring
  have h1 : componentSpan (gapF c) 1 = 1 := by
    calc _ = (1 - 0 : ℝ) := componentSpan_from_extrema (gapF c) 1 1 0
          (by intro a; fin_cases a <;> simp [gapF] <;> linarith)
          (by intro a; fin_cases a <;> simp [gapF] <;> linarith) 1 0
          (by simp [gapF] <;> linarith) (by simp [gapF] <;> linarith)
      _ = 1 := by norm_num
  have h2 : componentSpan (gapF c) 2 = c := by
    calc _ = (c - 0 : ℝ) := componentSpan_from_extrema (gapF c) 2 c 0
          (by intro a; fin_cases a <;> simp [gapF] <;> linarith)
          (by intro a; fin_cases a <;> simp [gapF] <;> linarith) 1 0
          (by simp [gapF] <;> linarith) (by simp [gapF] <;> linarith)
      _ = c := by norm_num
  rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) j with h | h | h
  · rw [h, h0]; linarith
  · rw [h, h1]; norm_num
  · rw [h, h2]; linarith

/-- `epsilon_nest (gapF c) = (c-1)/(2c+1)` exactly, for every real `c ≥ 1`. -/
theorem gap_normalized_threshold (hc : 1 ≤ c) :
    NormalizedNestingThreshold (gapF c) ((c - 1) / (2 * c + 1)) := by
  have hD : (0:ℝ) < 2 * c + 1 := by linarith
  have := normalized_threshold_of_selected (gapF c) (2 * c + 1) ((c - 1) / 2) hD
    (gap_modularSpan hc) (gap_threshold hc)
  have hEq : 2 * ((c - 1) / 2) / (2 * c + 1) = (c - 1) / (2 * c + 1) := by
    field_simp
  rwa [hEq] at this

/-- `epsilon_nest^star ≥ 1/2` even over instances with every component
non-constant: the family `gapF c` approaches `1/2` from below. -/
theorem gap_sup_half (delta : ℝ) (hdelta : 0 < delta) :
    ∃ c : ℝ, 1 ≤ c ∧ (∀ j : Fin 3, 0 < componentSpan (gapF c) j) ∧
      1 / 2 - delta < (c - 1) / (2 * c + 1) ∧
      NormalizedNestingThreshold (gapF c) ((c - 1) / (2 * c + 1)) := by
  have hpos : 0 < 3 / delta := by positivity
  set c : ℝ := 1 + 3 / delta with hcdef
  have hc : 1 ≤ c := by rw [hcdef]; linarith
  have hD : (0:ℝ) < 2 * c + 1 := by linarith
  have hprod : delta * c = delta + 3 := by
    rw [hcdef]; field_simp
  refine ⟨c, hc, gap_all_components_nonconstant hc, ?_, gap_normalized_threshold hc⟩
  rw [lt_div_iff₀ hD]
  have hexp : (1 / 2 - delta) * (2 * c + 1) = c + 1 / 2 - 2 * (delta * c) - delta := by
    ring
  rw [hexp, hprod]
  linarith

end

end CIGAMF.P13.StructuralNestingThreshold

/-! ## Axiom audit: every theorem stated in this file -/

#print axioms CIGAMF.P13.StructuralNestingThreshold.selectedRadius_nonneg
#print axioms CIGAMF.P13.StructuralNestingThreshold.normalizedRadius_eq_selectedRadius_div
#print axioms CIGAMF.P13.StructuralNestingThreshold.scale_ineq
#print axioms CIGAMF.P13.StructuralNestingThreshold.epsilonOptimalAt_div
#print axioms CIGAMF.P13.StructuralNestingThreshold.normalized_threshold_of_selected
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_compl_empty
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_compl_univ
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_compl_0
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_compl_1
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_compl_2
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_compl_3
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_compl_01
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_compl_02
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_compl_03
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_compl_12
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_compl_13
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_compl_23
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_compl_012
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin3_compl_empty
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin3_compl_univ
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_card_one
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin4_card_two
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin3_card_one
#print axioms CIGAMF.P13.StructuralNestingThreshold.fin3_card_two
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_r_empty
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_r0
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_r1
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_r2
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_r3
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_r01
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_r02
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_r03
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_r12
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_r13
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_r23
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_r012
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_runiv
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_full
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_prefix0
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_prefix1
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_prefix2
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_prefix3
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_prefix4
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_chain_half
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_no_chain_below_half
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_threshold
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_modularSpan
#print axioms CIGAMF.P13.StructuralNestingThreshold.nest_normalized_threshold
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_r_empty
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_r0
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_r1
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_r2
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_r01
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_r02
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_r12
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_runiv
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_full
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_prefix0
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_prefix1
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_prefix2
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_prefix3
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_chain_half
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_no_chain_below_half
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_threshold
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_modularSpan
#print axioms CIGAMF.P13.StructuralNestingThreshold.dead_normalized_threshold
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_r_empty
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_r0
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_r1
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_r2
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_r01
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_r02
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_r12
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_runiv
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_full
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_prefix0
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_prefix1
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_prefix2
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_prefix3
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_chain
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_no_chain_below
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_threshold
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_modularSpan
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_all_components_nonconstant
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_normalized_threshold
#print axioms CIGAMF.P13.StructuralNestingThreshold.gap_sup_half

