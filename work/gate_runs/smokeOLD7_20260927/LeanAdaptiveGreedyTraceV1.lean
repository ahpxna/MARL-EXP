import Mathlib.Tactic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Adaptive: the greedy rule, as a FUNCTION, reaches the witness counts.

## WHY THIS MODULE EXISTS

`LeanAdaptiveOnlineQuotaFailsV1.greedy_steps` concludes `True`.  Its eleven comparisons are
real and are kernel-checked, but they live inside the proof and nothing about them escapes
into a statement, so the identification of the count vector `N` as *the trajectory the
largest-deficit rule produces* rested on a recomputation reported in prose rather than on a
theorem.  That was the one place where the Adaptive paper's claim was broader than its
artifact.

This module closes it.  The rule is defined as a function and the trajectory is computed by
the kernel, so `greedy_reaches_witness` says exactly what the prose said:

    running largest-deficit-first on w = (17,1,1,3,1)/23 for 11 steps
    produces the counts (7,1,1,1,1),

and `greedy_deficit_exceeds_one` states the violation on *that* trajectory rather than on a
count vector supplied by hand.

## THE ONE DESIGN DECISION

Everything is in `ℤ`, not `ℚ`.  Every weight here has denominator `23`, so the deficit
`t * w i - N i` equals `(t * p i - N i * 23) / 23`, and the rule -- which only ever compares
deficits with each other -- can be run on the numerators alone.  That keeps the computation
inside decidable integer arithmetic, so `decide` discharges it and the axiom set stays
`{propext, Classical.choice, Quot.sound}`.

`native_decide` would also discharge these and is deliberately NOT used: it adds
`Lean.ofReduceBool` to the axioms, which would fail the acceptance contract this corpus is
audited against.  The price is `maxRecDepth`, set below.

Ties go to the smaller index, matching the convention of the reported trace.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace CIGAMF.P13.AdaptiveGreedyTrace

/-- Numerators of the five-arm witness target `w = (17,1,1,3,1)/23`. -/
def p : Fin 5 → ℤ := ![17, 1, 1, 3, 1]

/-- The common denominator of the witness target. -/
def den : ℤ := 23

/-- Keep whichever of two arms has the larger scaled deficit, ties to the first. -/
def pick (v : Fin 5 → ℤ) (a b : Fin 5) : Fin 5 := if v a < v b then b else a

/-- The arm a largest-deficit rule serves, given the scaled deficits `v`.

Ties go to the smaller index: the fold replaces the incumbent only on a strict increase.
`pick` is a top-level definition rather than a `let` so that the maximality lemma below can
unfold it; as a `let` inside `best` it did not reduce and the proof failed. -/
def best (v : Fin 5 → ℤ) : Fin 5 := pick v (pick v (pick v (pick v 0 1) 2) 3) 4

/-- Scaled deficit of arm `i` at time `t` under counts `N`: this is `den * (t * w i - N i)`,
and scaling by the positive `den` does not change which arm is maximal. -/
def deficit (N : Fin 5 → ℤ) (t : ℤ) (i : Fin 5) : ℤ := t * p i - N i * den

/-- Counts as an explicit five-tuple.

`Fin 5 -> Z` with `Function.update` is the natural phrasing and the kernel will not reduce
it in reasonable time: each step forces five decidable equality tests on `Fin 5` underneath
eleven layers of recursion, and `decide` ran for minutes without finishing. A tuple reduces
by pattern matching alone, and the run completes in seconds. The Fin-indexed reading is
recovered by `toFun` below, so nothing is lost but the reduction cost. -/
abbrev St : Type := ℤ × ℤ × ℤ × ℤ × ℤ

/-- Read a count tuple as a function on arms. -/
def toFun (N : St) : Fin 5 → ℤ := ![N.1, N.2.1, N.2.2.1, N.2.2.2.1, N.2.2.2.2]

/-- Serve arm `i`, adding one pull to its count. -/
def bump (N : St) : Fin 5 → St
  | 0 => (N.1 + 1, N.2)
  | 1 => (N.1, N.2.1 + 1, N.2.2)
  | 2 => (N.1, N.2.1, N.2.2.1 + 1, N.2.2.2)
  | 3 => (N.1, N.2.1, N.2.2.1, N.2.2.2.1 + 1, N.2.2.2.2)
  | 4 => (N.1, N.2.1, N.2.2.1, N.2.2.2.1, N.2.2.2.2 + 1)

/-- Largest-deficit-first, run for `n` steps from the empty allocation. -/
def greedy : ℕ → St
  | 0 => (0, 0, 0, 0, 0)
  | (n + 1) =>
      let N := greedy n
      bump N (best (deficit (toFun N) (n : ℤ)))

/-- The counts the paper reports at horizon eleven. -/
def witnessCounts : St := (7, 1, 1, 1, 1)

/-- **The rule-to-counts link.**  Running the largest-deficit rule for eleven steps on the
witness target produces exactly the reported counts.  This is what `greedy_steps : True`
did not say. -/
theorem greedy_reaches_witness : greedy 11 = witnessCounts := by
  decide

/-- The trajectory spends exactly the horizon: eleven pulls, distributed as reported. -/
theorem greedy_counts_sum :
    (greedy 11).1 + (greedy 11).2.1 + (greedy 11).2.2.1
      + (greedy 11).2.2.2.1 + (greedy 11).2.2.2.2 = 11 := by
  decide

/-- The scaled deficit of arm `0` on the trajectory the rule produces is `26`. -/
theorem greedy_deficit_value : deficit (toFun (greedy 11)) 11 0 = 26 := by
  decide

/-- **The deficit at horizon eleven exceeds one**, on the trajectory the rule actually
produces: the scaled deficit of arm `0` is `26` against the scaled bound `den = 23`, i.e.
`11 * w 0 - N 0 = 26/23 > 1`. -/
theorem greedy_deficit_exceeds_one : deficit (toFun (greedy 11)) 11 0 > den := by
  decide

/-- `pick` never decreases the incumbent's value. -/
theorem le_pick_left (v : Fin 5 → ℤ) (a b : Fin 5) : v a ≤ v (pick v a b) := by
  unfold pick; split_ifs with h <;> omega

/-- `pick` dominates the challenger's value too. -/
theorem le_pick_right (v : Fin 5 → ℤ) (a b : Fin 5) : v b ≤ v (pick v a b) := by
  unfold pick; split_ifs with h <;> omega

/-- `best` really does return an index of maximal value.  Proved once, from the definition,
rather than re-checked at each of eleven steps. -/
theorem best_is_max (v : Fin 5 → ℤ) (j : Fin 5) : v j ≤ v (best v) := by
  unfold best
  fin_cases j
  · exact le_trans (le_pick_left v 0 1)
      (le_trans (le_pick_left v _ 2) (le_trans (le_pick_left v _ 3) (le_pick_left v _ 4)))
  · exact le_trans (le_pick_right v 0 1)
      (le_trans (le_pick_left v _ 2) (le_trans (le_pick_left v _ 3) (le_pick_left v _ 4)))
  · exact le_trans (le_pick_right v _ 2)
      (le_trans (le_pick_left v _ 3) (le_pick_left v _ 4))
  · exact le_trans (le_pick_right v _ 3) (le_pick_left v _ 4)
  · exact le_pick_right v _ 4

/-- **Every step of the trajectory is a genuine largest-deficit choice**, at every horizon
and not only at the eleven the witness needs.  This is what the eleven hand-written
comparisons were checking, now as a statement rather than inside a proof. -/
theorem greedy_step_is_maximal (n : ℕ) (j : Fin 5) :
    deficit (toFun (greedy n)) (n : ℤ) j
      ≤ deficit (toFun (greedy n)) (n : ℤ) (best (deficit (toFun (greedy n)) (n : ℤ))) :=
  best_is_max _ j

end CIGAMF.P13.AdaptiveGreedyTrace

#print axioms CIGAMF.P13.AdaptiveGreedyTrace.greedy_reaches_witness
#print axioms CIGAMF.P13.AdaptiveGreedyTrace.greedy_deficit_exceeds_one
#print axioms CIGAMF.P13.AdaptiveGreedyTrace.greedy_step_is_maximal
