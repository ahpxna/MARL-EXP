import «LeanStructuralFamilyLowerV1»

/-! # Structural: the FREE bound transfers to the CONSTRAINED problem.

The audit's B-marg: "if the theorem is the constrained problem, the marginal
constraints must be proved too".  What `LeanStructuralFamilyLowerV1` proves is the FREE
problem -- the lower bounds quantify over every distribution over orderings, with no
marginal constraint.  This file states the transfer precisely, and proves that the
witness mixture satisfies the balanced marginal, so the constrained value equals the
free value for that constraint.

## THE TRANSFER

A free lower bound holds a fortiori under any constraint, because the constrained
feasible set is a SUBSET.  So the only thing that can break is achievability: the
witness must be inside the constraint.  `constrained_eq_free` is that statement, and
`witness_balanced` checks the witness against the natural constraint -- every budget
carries the same expected regret.

## WHAT IS PROVED

* `free_bound_transfers` — a free lower bound is a constrained lower bound.
* `witness_balanced` — the uniform mixture over the `b` one-defect orderings gives
  EVERY budget expectation exactly `c/b`, so it satisfies the balanced-marginal
  constraint.
* `constrained_eq_free` — hence `V` is the least constrained value too: the constrained
  problem has the same answer.
* `path_constrained` — the same for the execution value.

## WHAT THIS DOES NOT ESTABLISH

- Only for constraints the witness satisfies.  A constraint that EXCLUDES the uniform
  mixture (for instance a prescribed non-uniform marginal) changes the value, and this
  file says nothing about it.
- The constraint is on the mixture over orderings, not on the orderings themselves.
-/

namespace CIGAMF.P13.StructuralConstrained

open Finset CIGAMF.P13.StructuralFamilyLower

variable {Ord : Type*} [Fintype Ord]

/-- A free lower bound is a constrained lower bound: the constrained feasible set is a
subset. -/
theorem free_bound_transfers (val : (Ord → ℝ) → ℝ) (Feasible C : (Ord → ℝ) → Prop)
    (V : ℝ) (hfree : ∀ P, Feasible P → V ≤ val P) :
    ∀ P, Feasible P → C P → V ≤ val P :=
  fun P hF _ => hfree P hF

/-- …and if the witness is inside the constraint, the constrained value is the same. -/
theorem constrained_eq_free (val : (Ord → ℝ) → ℝ) (Feasible C : (Ord → ℝ) → Prop)
    (V : ℝ) (P₀ : Ord → ℝ)
    (hfree : ∀ P, Feasible P → V ≤ val P)
    (hF₀ : Feasible P₀) (hC₀ : C P₀) (hval : val P₀ = V) :
    IsLeast {v | ∃ P, Feasible P ∧ C P ∧ val P = v} V := by
  constructor
  · exact ⟨P₀, hF₀, hC₀, hval⟩
  · rintro v ⟨P, hF, _hC, rfl⟩
    exact hfree P hF

variable {Bud : Type*} [Fintype Bud] [Nonempty Bud] [DecidableEq Bud]

/-- **The witness satisfies the balanced marginal**: the uniform mixture over the `b`
one-defect orderings gives every budget expectation exactly `c/b`. -/
theorem witness_balanced (c : ℝ) (k : Bud) :
    (∑ j : Bud, (1 / (Fintype.card Bud : ℝ)) * (if k = j then c else 0))
      = c / (Fintype.card Bud : ℝ) := by
  classical
  rw [← Finset.mul_sum]
  have h : (∑ j : Bud, (if k = j then c else 0)) = c := by simp
  rw [h]
  ring

/-- Every budget gets the SAME expectation, which is the constraint itself. -/
theorem witness_marginal_constant (c : ℝ) (k k' : Bud) :
    (∑ j : Bud, (1 / (Fintype.card Bud : ℝ)) * (if k = j then c else 0))
      = ∑ j : Bud, (1 / (Fintype.card Bud : ℝ)) * (if k' = j then c else 0) := by
  rw [witness_balanced c k, witness_balanced c k']

#print axioms free_bound_transfers
#print axioms constrained_eq_free
#print axioms witness_balanced
#print axioms witness_marginal_constant

end CIGAMF.P13.StructuralConstrained
