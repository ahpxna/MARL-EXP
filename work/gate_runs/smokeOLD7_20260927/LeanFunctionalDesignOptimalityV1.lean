import Mathlib

/-! # Functional: what `J(w*)` is, and what it is NOT.

The audit's standing warning: `A d²/2` is the value AT the allocation `w*`, and writing
`Γ* = sup_w J(w)` for it is an over-claim.  This file makes the gap between the two a
theorem rather than a caveat, and supplies the test a search has to pass.

## THE SHAPE OF THE PROBLEM

`J(w) = min_λ ∑_e w_e I_λ(e)` is a minimum of LINEAR functions of `w`, hence CONCAVE on
the budget simplex.  Two consequences:

* `J(w*) ≤ sup_w J(w)` always, with equality only if `w*` is a maximiser -- which is
  what has NOT been shown;
* concavity makes the segment bound `J((1-α)w + α δ_k) ≥ (1-α)J(w) + α·min_λ I_λ(k)`
  exact, so a single cell `k` with `min_λ I_λ(k) > J(w)` DISPROVES optimality outright,
  for every `α ∈ (0,1]` -- no derivative, no small-`α` argument.

## WHAT IS PROVED

* `value_min_linear_concave` — `J` is concave: the segment value is at least the chord.
* `segment_lower` — the explicit segment bound towards a single cell.
* `not_optimal_of_better_cell` — **if some cell beats the current value against EVERY
  alternative, the design is not optimal**, and the improvement is strict for every
  step size.
* `value_le_sup` — `J(w*) ≤ sup_w J(w)`: the direction that always holds, and the only
  one the Functional results support.
* `optimal_iff_no_better_direction` — the converse packaging: `w` is a maximiser exactly
  when no mixture of cells beats it, which is the statement a numerical search must
  certify.

## WHAT THIS DOES NOT ESTABLISH

- That `w*` IS or IS NOT a maximiser.  `not_optimal_of_better_cell` is a sufficient
  condition for failure that does not fire at `w*` (for each cell there is an
  alternative that leaves it unmoved, so `min_λ I_λ(k) = 0`).  The decisive test is the
  full equivalence condition over MIXTURES of active alternatives, computed in
  `scripts/P23_functional_design_optimum.py`.
- Nothing here computes `sup_w J(w)`.
-/

namespace CIGAMF.P13.FunctionalDesignOptimality

open Finset

variable {Cell Alt : Type*} [Fintype Cell] [Fintype Alt] [Nonempty Alt] [DecidableEq Cell]

/-- The design value: the worst alternative's energy. -/
noncomputable def value (I : Alt → Cell → ℝ) (w : Cell → ℝ) : ℝ :=
  (univ : Finset Alt).inf' univ_nonempty (fun l => ∑ e, w e * I l e)

/-- `J` is concave: a minimum of linear functions. -/
theorem value_min_linear_concave (I : Alt → Cell → ℝ) (w v : Cell → ℝ) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (1 - a) * value I w + a * value I v ≤ value I (fun e => (1 - a) * w e + a * v e) := by
  classical
  refine Finset.le_inf' _ _ fun l _ => ?_
  have hw : value I w ≤ ∑ e, w e * I l e := Finset.inf'_le _ (mem_univ l)
  have hv : value I v ≤ ∑ e, v e * I l e := Finset.inf'_le _ (mem_univ l)
  have hsplit : (∑ e, ((1 - a) * w e + a * v e) * I l e)
      = (1 - a) * (∑ e, w e * I l e) + a * (∑ e, v e * I l e) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [hsplit]
  have h1 : (1 - a) * value I w ≤ (1 - a) * (∑ e, w e * I l e) :=
    mul_le_mul_of_nonneg_left hw (by linarith)
  have h2 : a * value I v ≤ a * (∑ e, v e * I l e) :=
    mul_le_mul_of_nonneg_left hv ha0
  linarith

/-- The segment bound towards a single cell `k`. -/
theorem segment_lower (I : Alt → Cell → ℝ) (w : Cell → ℝ) (k : Cell) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (1 - a) * value I w + a * ((univ : Finset Alt).inf' univ_nonempty (fun l => I l k))
      ≤ value I (fun e => (1 - a) * w e + a * (if e = k then 1 else 0)) := by
  classical
  have hv : value I (fun e => if e = k then (1:ℝ) else 0)
      = (univ : Finset Alt).inf' univ_nonempty (fun l => I l k) := by
    unfold value
    congr 1
    funext l
    simp
  have := value_min_linear_concave I w (fun e => if e = k then (1:ℝ) else 0) a ha0 ha1
  rwa [hv] at this

/-- **A cell that beats the current value against EVERY alternative disproves
optimality**, and the improvement is strict for every step size in `(0,1]`. -/
theorem not_optimal_of_better_cell (I : Alt → Cell → ℝ) (w : Cell → ℝ) (k : Cell) (a : ℝ)
    (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hbetter : value I w < (univ : Finset Alt).inf' univ_nonempty (fun l => I l k)) :
    value I w < value I (fun e => (1 - a) * w e + a * (if e = k then 1 else 0)) := by
  have hseg := segment_lower I w k a (le_of_lt ha0) ha1
  nlinarith [hseg, hbetter, ha0]

/-- The direction that always holds: the value at a named allocation is a LOWER bound
for the design optimum.  This is the only inequality the Functional results support. -/
theorem value_le_sup (I : Alt → Cell → ℝ) (wstar : Cell → ℝ) (Gamma : ℝ)
    (hsup : ∀ w, value I w ≤ Gamma) : value I wstar ≤ Gamma := hsup wstar

/-- The packaging a numerical search must certify: `w` is a maximiser exactly when no
design beats it. -/
theorem optimal_iff_no_better_direction (I : Alt → Cell → ℝ) (w : Cell → ℝ) :
    (∀ v, value I v ≤ value I w) ↔ IsGreatest (Set.range (value I)) (value I w) := by
  constructor
  · intro h
    exact ⟨⟨w, rfl⟩, by rintro x ⟨v, rfl⟩; exact h v⟩
  · rintro ⟨_, hub⟩ v
    exact hub ⟨v, rfl⟩

#print axioms value_min_linear_concave
#print axioms segment_lower
#print axioms not_optimal_of_better_cell
#print axioms value_le_sup
#print axioms optimal_iff_no_better_direction

end CIGAMF.P13.FunctionalDesignOptimality
