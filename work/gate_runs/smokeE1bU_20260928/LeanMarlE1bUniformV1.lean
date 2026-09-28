import Mathlib
import «LeanMarlE1bRealizationV1»

/-!
# E1b: a UNIFORM shift halves the ScoreLocal constant without knowing the interacting pair

`LeanMarlE1bRealizationV1.e1b_scoreLocal_half` halves the constant with the pair-dependent score
`g² + [i ∈ E]·β²/2`.  A deployable learner does not know `E`, so that score must not be read as a
learned score that knows the pair for free (readiness audit §5).  Here the SAME constant `β²/2` is
obtained with the score `g² + β²/2` for EVERY message: the marginal is `g²_i + I·β²` with `I ∈ {0,1}`,
and `|I·β² − β²/2| = β²/2`.  The uniform shift preserves every ranking of the scores.

## WHAT IS PROVED
* `e1b_scoreLocal_uniform` — `ScoreLocal (e1bValue g2 β2 σ2 E) (fun i => g2 i + β2/2) (β2/2)`, no
  hypothesis on `E`.
* `uniform_shift_order` — the shifted score orders messages exactly as `g2` does.
* `e1b_uniform_satisfiable` — a concrete instance with `β2 > 0` and a two-element `E`.

## WHAT THIS DOES NOT ESTABLISH
- Anything about the observation law or a learned score's error `u`; this is the mean-value
  structure only.  No traffic guarantee.
-/

namespace CIGAMF.P13.MarlE1bUniform

open Finset CIGAMF.P13.MarlEstimatedRevision CIGAMF.P13.MarlE1bRealization

variable {m : ℕ}

/-- **The uniform shift gives the halved constant for every interacting set `E`.** -/
theorem e1b_scoreLocal_uniform (g2 : Fin m → ℝ) (β2 σ2 : ℝ) (E : Finset (Fin m)) (hβ : 0 ≤ β2) :
    ScoreLocal (e1bValue g2 β2 σ2 E) (fun i => g2 i + β2 / 2) (β2 / 2) := by
  intro A i hi
  rw [e1b_marginal g2 β2 σ2 E A i hi]
  beta_reduce
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- **The shift does not change any ranking.** -/
theorem uniform_shift_order (g2 : Fin m → ℝ) (c : ℝ) (i j : Fin m) :
    g2 i + c ≤ g2 j + c ↔ g2 i ≤ g2 j := add_le_add_iff_right c

theorem e1b_uniform_satisfiable :
    ScoreLocal (e1bValue (fun _ : Fin 4 => (1 : ℝ)) (8 / 5) (1 / 4) {0, 1}) (fun _ => 1 + (8 / 5) / 2) ((8 / 5) / 2) ∧
      (0 : ℝ) < 8 / 5 :=
  ⟨e1b_scoreLocal_uniform (fun _ : Fin 4 => (1 : ℝ)) (8 / 5) (1 / 4) {0, 1} (by norm_num), by norm_num⟩

end CIGAMF.P13.MarlE1bUniform

#print axioms CIGAMF.P13.MarlE1bUniform.e1b_scoreLocal_uniform
#print axioms CIGAMF.P13.MarlE1bUniform.uniform_shift_order
#print axioms CIGAMF.P13.MarlE1bUniform.e1b_uniform_satisfiable
