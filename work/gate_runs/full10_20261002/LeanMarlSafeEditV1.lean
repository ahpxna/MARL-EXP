import Mathlib

/-!
# When may a selector with an estimated value leave the committed prefix?

`f` is the true value of a candidate profile, `fh` an estimate with `|fh − f| ≤ ε` on the two profiles
involved, `P` the committed prefix.  Argmax stability (the `2ε` of
`LeanMarlEstimatedRevisionV1.deployed_regret`) in the form a deployed selector needs:

## WHAT IS PROVED
* `safe_edit` — if the estimated gain over `P` exceeds `2ε`, the edit is a TRUE improvement.
* `safe_rule_never_harms` — the rule "edit only if the estimated gain exceeds `2ε`" is never worse than `P`.
* `argmax_harm_le` — an argmax of `fh` (any profile with `fh ≥ fh P`) loses at most `2ε` against `P`.
* `argmax_harm_sharp` — that `2ε` loss is attained by an argmax (a tie at estimated gain 0).
* `threshold_sharp` — for EVERY threshold `τ < 2ε` the rule "edit if the estimated gain exceeds `τ`" can
  harm: an instance with per-value error `ε`, estimated gain above `τ` and a strictly worse edit.  So `2ε` is
  the smallest threshold that never harms (28/09 self-audit: the old docstring claimed this from the tie
  witness alone, which covers only `τ < 0`).
* `threshold_sharp_positive` — the instance `ε = 1`, `τ = 1`: a POSITIVE threshold below `2ε` still harms.
* `safe_hypotheses_satisfiable` — a concrete instance with `ε > 0` and a strictly improving edit.

## WHAT THIS DOES NOT ESTABLISH
- Any bound on `ε` for a learned critic (that is data, or T2's calibration class).
- That the safe rule gains anything: with `2ε` above every available gain it never edits.
-/

namespace CIGAMF.P13.MarlSafeEdit

variable {α : Type*}

theorem safe_edit (f fh : α → ℝ) (P S : α) (ε : ℝ)
    (hP : |fh P - f P| ≤ ε) (hS : |fh S - f S| ≤ ε) (hgap : fh S - fh P > 2 * ε) : f S > f P := by
  rw [abs_le] at hP hS
  linarith [hP.1, hP.2, hS.1, hS.2]

theorem safe_rule_never_harms (f fh : α → ℝ) (P S : α) (ε : ℝ)
    (hP : |fh P - f P| ≤ ε) (hS : |fh S - f S| ≤ ε) :
    f P ≤ f (if fh S - fh P > 2 * ε then S else P) := by
  split_ifs with h
  · exact le_of_lt (safe_edit f fh P S ε hP hS h)
  · exact le_refl _

theorem argmax_harm_le (f fh : α → ℝ) (P S : α) (ε : ℝ)
    (hP : |fh P - f P| ≤ ε) (hS : |fh S - f S| ≤ ε) (hmax : fh P ≤ fh S) : f P - f S ≤ 2 * ε := by
  rw [abs_le] at hP hS
  linarith [hP.1, hP.2, hS.1, hS.2]

/-- The `2ε` loss is attained: `f P = 1`, `f S = −1`, both estimated at `0`, `ε = 1`. -/
theorem argmax_harm_sharp :
    let f : Bool → ℝ := fun b => if b then -1 else 1
    let fh : Bool → ℝ := fun _ => 0
    |fh false - f false| ≤ 1 ∧ |fh true - f true| ≤ 1 ∧ fh false ≤ fh true ∧ f false - f true = 2 * 1 := by
  norm_num

theorem safe_hypotheses_satisfiable :
    let f : Bool → ℝ := fun b => if b then 5 else 0
    let fh : Bool → ℝ := fun b => if b then 4 else 1
    |fh false - f false| ≤ 1 ∧ |fh true - f true| ≤ 1 ∧ fh true - fh false > 2 * 1 ∧ f true > f false := by
  norm_num

/-- **Every threshold below `2ε` can harm.**  With `g = (τ + 2ε)/2`: `f P = ε`, `f S = τ/2`, `fh P = 0`,
`fh S = g`; both errors are exactly `ε`, the estimated gain `g` exceeds `τ`, and `f S < f P` because `τ < 2ε`. -/
theorem threshold_sharp (ε τ : ℝ) (hε : 0 ≤ ε) (hτ : τ < 2 * ε) :
    ∃ f fh : Bool → ℝ, |fh false - f false| ≤ ε ∧ |fh true - f true| ≤ ε ∧
      fh true - fh false > τ ∧ f true < f false := by
  refine ⟨fun b => cond b (τ / 2) ε, fun b => cond b ((τ + 2 * ε) / 2) 0, ?_, ?_, ?_, ?_⟩
  · show |(0 : ℝ) - ε| ≤ ε
    rw [zero_sub, abs_neg, abs_of_nonneg hε]
  · show |(τ + 2 * ε) / 2 - τ / 2| ≤ ε
    rw [abs_le]; constructor <;> linarith
  · show (τ + 2 * ε) / 2 - 0 > τ
    linarith
  · show τ / 2 < ε
    linarith

/-- The hypotheses of `threshold_sharp` are met with a POSITIVE threshold: `ε = 1`, `τ = 1`. -/
theorem threshold_sharp_positive :
    ∃ f fh : Bool → ℝ, |fh false - f false| ≤ 1 ∧ |fh true - f true| ≤ 1 ∧
      fh true - fh false > 1 ∧ f true < f false :=
  threshold_sharp 1 1 (by norm_num) (by norm_num)

end CIGAMF.P13.MarlSafeEdit

#print axioms CIGAMF.P13.MarlSafeEdit.safe_edit
#print axioms CIGAMF.P13.MarlSafeEdit.safe_rule_never_harms
#print axioms CIGAMF.P13.MarlSafeEdit.argmax_harm_le
#print axioms CIGAMF.P13.MarlSafeEdit.argmax_harm_sharp
#print axioms CIGAMF.P13.MarlSafeEdit.safe_hypotheses_satisfiable
#print axioms CIGAMF.P13.MarlSafeEdit.threshold_sharp
#print axioms CIGAMF.P13.MarlSafeEdit.threshold_sharp_positive
