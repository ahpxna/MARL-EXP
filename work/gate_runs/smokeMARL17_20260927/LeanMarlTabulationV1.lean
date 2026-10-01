import Mathlib
import «LeanMarlEstimatedRevisionV1»

/-!
# The latency-premise check of PROTOCOL_v1: per-budget tabulation dominates revision

Under PROTOCOL_v1 a budget-conditioned selector sees the grant `k` at the same moment as the
revision method and has the same precompute allowance.  The set of possible grants is finite,
so it can compute a table `k ↦ Ŝ(k)` BEFORE the grant and answer by lookup afterwards.  This
module proves the value side of that observation; the timing side is measured, not proved.

## WHAT IS PROVED

* `reach_card` — every set reachable by revision is a k-set, for every prefix and every `R`.
  Revision is a restriction of per-budget selection, never an enlargement.
* `tabulated_regret` — a per-budget table built from ANY evaluator with error `ε` on the
  k-sets and search error `ν` has regret at most `2ε + ν` against EVERY k-set.  No
  interaction constant, no score error, no revision count: the geometric term
  `2(δ+u)(d − R)₊` of `deployed_regret` is absent.
* `tabulation_dominates_revision` — with the same evaluator, the table's evaluator value is
  at least that of any revision output, up to `ν`.
* `exact_tabulation_dominates` — with the true values, the exact table is at least as good
  as every revision output of every prefix at every `R`.
* `tabulation_regret_sharp` — the `2ε` is attained, so tabulation is not free of estimation
  error; it is free of the geometric term only.

## WHAT THIS DOES NOT ESTABLISH

- Anything about wall-clock time.  That the table is computed before the grant and read
  after it is a property of the protocol, measured in the latency benchmark.
- That tabulation is cheap to LEARN.  A per-budget selector may need more data or
  generalise worse to unseen grants than one priority plus a repair; that is the question
  left for the experiments, and the only place a prepared priority can still win under
  PROTOCOL_v1.
- Anything about protocols where nesting is physically forced (one broadcast stream read by
  receivers with different budgets, or a channel cut at an unknown time).  There the
  per-budget table is not feasible, and this module does not apply.
-/

namespace CIGAMF.P13.MarlTabulation

open Finset CIGAMF.P13.MarlEstimatedRevision

variable {m : ℕ}

/-- Every revision output is a k-set. -/
theorem reach_card (P S : Finset (Fin m)) (k R : ℕ) (h : Reach P k R S) : S.card = k := h.1

/-- **Tabulation regret.**  `L` is the family of all k-sets actually tabulated. -/
theorem tabulated_regret (f fh : Finset (Fin m) → ℝ) (eps nu : ℝ) (k : ℕ)
    (L : Finset (Finset (Fin m))) (hL : ∀ S, S.card = k → S ∈ L)
    (Shat : Finset (Fin m)) (hShat : Shat ∈ L)
    (hEval : ∀ S ∈ L, |fh S - f S| ≤ eps) (hSearch : ∀ S ∈ L, fh S ≤ fh Shat + nu)
    (T : Finset (Fin m)) (hT : T.card = k) :
    f T - f Shat ≤ 2 * eps + nu := by
  have hTL := hL T hT
  have e1 := (abs_le.mp (hEval T hTL)).1
  have e2 := (abs_le.mp (hEval Shat hShat)).2
  have s1 := hSearch T hTL
  linarith

/-- **The table beats any revision output on the same evaluator**, up to the search error. -/
theorem tabulation_dominates_revision (fh : Finset (Fin m) → ℝ) (nu : ℝ) (k R : ℕ)
    (P : Finset (Fin m)) (L : Finset (Finset (Fin m))) (hL : ∀ S, S.card = k → S ∈ L)
    (Shat : Finset (Fin m)) (hSearch : ∀ S ∈ L, fh S ≤ fh Shat + nu)
    (Srev : Finset (Fin m)) (hrev : Reach P k R Srev) :
    fh Srev ≤ fh Shat + nu :=
  hSearch Srev (hL Srev (reach_card P Srev k R hrev))

/-- **With true values, the exact table dominates every prefix and every `R`.** -/
theorem exact_tabulation_dominates (f : Finset (Fin m) → ℝ) (k : ℕ)
    (Tstar : Finset (Fin m)) (hstar : ∀ S : Finset (Fin m), S.card = k → f S ≤ f Tstar)
    (P : Finset (Fin m)) (R : ℕ) (Srev : Finset (Fin m)) (hrev : Reach P k R Srev) :
    f Srev ≤ f Tstar :=
  hstar Srev (reach_card P Srev k R hrev)

/-- **The `2ε` of tabulation is attained**: two 1-sets, true values `0` and `2ε`, each
evaluated `ε` toward the other, and the evaluator's argmax picks the worse. -/
theorem tabulation_regret_sharp (eps : ℝ) (heps : 0 ≤ eps) :
    ∃ (f fh : Finset (Fin 2) → ℝ) (L : Finset (Finset (Fin 2))) (Shat T : Finset (Fin 2)),
      (∀ S : Finset (Fin 2), S.card = 1 → S ∈ L) ∧ Shat ∈ L ∧ T.card = 1 ∧
      (∀ S ∈ L, |fh S - f S| ≤ eps) ∧ (∀ S ∈ L, fh S ≤ fh Shat + 0) ∧
      f T - f Shat = 2 * eps := by
  refine ⟨fun S => if S = {1} then 2 * eps else 0, fun _ => eps, {{0}, {1}}, {0}, {1},
    ?_, by simp, by decide, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hS
    fin_cases a <;> simp
  · intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl
    · simp [abs_of_nonneg heps]
    · simp; rw [show eps - 2 * eps = -eps by ring, abs_neg, abs_of_nonneg heps]
  · intro S _; simp
  · simp

end CIGAMF.P13.MarlTabulation

#print axioms CIGAMF.P13.MarlTabulation.reach_card
#print axioms CIGAMF.P13.MarlTabulation.tabulated_regret
#print axioms CIGAMF.P13.MarlTabulation.tabulation_dominates_revision
#print axioms CIGAMF.P13.MarlTabulation.exact_tabulation_dominates
#print axioms CIGAMF.P13.MarlTabulation.tabulation_regret_sharp
