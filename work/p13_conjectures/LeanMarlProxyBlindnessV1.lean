import Mathlib
import «LeanMarlSubsetFrontierV1»

/-!
# "Enough power to repair" versus "enough information to repair correctly"

Two decision-value worlds on three messages, `w₁ = sharpF` and its mirror `w₂`.  They agree on
EVERY set of size at most one: the same empty value and the same singleton values, so all
first-order gains are `0`.  Both satisfy the local interaction bound with `δ = 7`.  At budget
`k = 2` their optimal sets differ: `{0,1}` in `w₁` and `{1,2}` in `w₂`.

## WHAT IS PROVED

* `mirror_local`, `worlds_agree_first_order` — both worlds are admissible (`δ = 7`) and
  indistinguishable by first-order (size ≤ 1) information.
* `oracle_one_revision` — STRUCTURAL SUFFICIENCY.  In both worlds, from ANY committed 2-set,
  one replacement reaches the optimum: an oracle with `R = 1` has regret `0`.
* `proxy_rule_regret` — INFORMATION INSUFFICIENCY.  Every rule that sees only first-order
  information returns the same 2-set in both worlds, so its worst-case regret is at least `4`.
  The revision power `R = 1` does not help, because the rule does not know which replacement
  to make.
* `proxy_mixture_regret` — the same bound for every randomised choice of 2-set:
  `max(E₁, E₂) ≥ 4`.
* `one_pair_query_suffices` — REPAIRED ACQUISITION.  Paying for ONE interaction measurement,
  the value of the pair `{0,1}`, identifies the world, and the rule "keep `{0,1}` if its value
  is positive, else `{1,2}`" has regret `0` in both.

This is the identifiability version of `V(N, R)` (MARL_PRIOR_ART_RECOURSE_AND_A_ROLE §4):
`V(first order, R = 1) ≥ 4 > 0 = V(first order + one pair, R = 1) = V(oracle, R = 1)`.

## WHAT THIS DOES NOT ESTABLISH

- Noisy measurements and sample costs, i.e. the log(1/δ) versus log²(1/δ) separation of
  paper A.  Here measurements are exact.
- A family on `m` messages with growing regret.  This is one exact witness.
-/

namespace CIGAMF.P13.MarlProxyBlindness

open CIGAMF.P13.MarlSubsetFrontier

/-- The mirror world: the roles of messages `0` and `2` are swapped. -/
def mirrorZ (S : Finset (Fin 3)) : ℤ :=
  if S = {1, 2} then 7 else if S = {0, 2} then 3 else if S = {0, 1} then -7 else 0

def mirrorF (S : Finset (Fin 3)) : ℝ := (mirrorZ S : ℝ)

theorem mirrorZ_local :
    ∀ (A : Finset (Fin 3)) (i : Fin 3), i ∉ A →
      |mirrorZ (insert i A) - mirrorZ A - (mirrorZ {i} - mirrorZ ∅)| ≤ 7 := by
  decide

theorem mirror_local : LocalInteraction mirrorF 7 := by
  intro A i hi
  have h := mirrorZ_local A i hi
  unfold gain mirrorF
  have hcast : ((mirrorZ (insert i A) : ℝ) - (mirrorZ A : ℝ) - ((mirrorZ {i} : ℝ) - (mirrorZ ∅ : ℝ))) =
      ((mirrorZ (insert i A) - mirrorZ A - (mirrorZ {i} - mirrorZ ∅) : ℤ) : ℝ) := by push_cast; ring
  rw [hcast, ← Int.cast_abs]
  exact_mod_cast h

theorem agree_first_orderZ : ∀ S : Finset (Fin 3), S.card ≤ 1 → sharpZ S = mirrorZ S := by
  decide

/-- The two worlds agree on every set of size at most one. -/
theorem worlds_agree_first_order : ∀ S : Finset (Fin 3), S.card ≤ 1 → sharpF S = mirrorF S := by
  intro S hS
  unfold sharpF mirrorF
  exact_mod_cast agree_first_orderZ S hS

/-- Regret tables at budget 2 (integer): best value 7 in each world. -/
theorem sharp_best : ∀ S : Finset (Fin 3), S.card = 2 → sharpZ S ≤ 7 := by decide
theorem mirror_best : ∀ S : Finset (Fin 3), S.card = 2 → mirrorZ S ≤ 7 := by decide

/-- Structural sufficiency: from any committed 2-set, one replacement reaches the optimum in
both worlds. -/
theorem oracle_one_revisionZ :
    ∀ P : Finset (Fin 3), P.card = 2 →
      (∃ S : Finset (Fin 3), S.card = 2 ∧ (S \ P).card ≤ 1 ∧ sharpZ S = 7) ∧
      (∃ S : Finset (Fin 3), S.card = 2 ∧ (S \ P).card ≤ 1 ∧ mirrorZ S = 7) := by
  decide

theorem oracle_one_revision (P : Finset (Fin 3)) (hP : P.card = 2) :
    (∃ S : Finset (Fin 3), S.card = 2 ∧ (S \ P).card ≤ 1 ∧ sharpF S = 7) ∧
      (∃ S : Finset (Fin 3), S.card = 2 ∧ (S \ P).card ≤ 1 ∧ mirrorF S = 7) := by
  obtain ⟨⟨S, h1, h2, h3⟩, ⟨T, g1, g2, g3⟩⟩ := oracle_one_revisionZ P hP
  exact ⟨⟨S, h1, h2, by unfold sharpF; exact_mod_cast h3⟩,
    ⟨T, g1, g2, by unfold mirrorF; exact_mod_cast g3⟩⟩

/-- Every 2-set has regret at least `4` in one of the two worlds. -/
theorem worst_regret_geZ : ∀ S : Finset (Fin 3), S.card = 2 →
    4 ≤ max (7 - sharpZ S) (7 - mirrorZ S) := by decide

/-- **Information insufficiency.**  A rule that sees only first-order information (it takes
equal outputs on value tables that agree on all sets of size ≤ 1) and returns a 2-set has
worst-case regret at least `4` on the two worlds.  The revision power `R = 1` is available
(`oracle_one_revision`); the rule lacks the information to use it. -/
theorem proxy_rule_regret (rule : (Finset (Fin 3) → ℝ) → Finset (Fin 3))
    (hfirst : ∀ f g : Finset (Fin 3) → ℝ, (∀ S, S.card ≤ 1 → f S = g S) → rule f = rule g)
    (hcard : ∀ f, (rule f).card = 2) :
    4 ≤ max (7 - sharpF (rule sharpF)) (7 - mirrorF (rule mirrorF)) := by
  have heq : rule sharpF = rule mirrorF := hfirst _ _ worlds_agree_first_order
  rw [← heq]
  have h := worst_regret_geZ (rule sharpF) (hcard sharpF)
  unfold sharpF mirrorF
  have : ((4 : ℤ) : ℝ) ≤ ((max (7 - sharpZ (rule sharpF)) (7 - mirrorZ (rule sharpF)) : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at this
  exact this

/-- The randomised version: any mixture `(a, b, c)` over the 2-sets `{0,1}`, `{1,2}`, `{0,2}`
has expected regret at least `4` in one of the two worlds. -/
theorem proxy_mixture_regret (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    4 ≤ max (a * 0 + b * 14 + c * 4) (a * 14 + b * 0 + c * 4) := by
  have h1 : (a * 0 + b * 14 + c * 4 + (a * 14 + b * 0 + c * 4)) / 2 ≤
      max (a * 0 + b * 14 + c * 4) (a * 14 + b * 0 + c * 4) := by
    have := le_max_left (a * 0 + b * 14 + c * 4) (a * 14 + b * 0 + c * 4)
    have := le_max_right (a * 0 + b * 14 + c * 4) (a * 14 + b * 0 + c * 4)
    linarith
  nlinarith

/-- The regret entries used in `proxy_mixture_regret` are the actual regrets. -/
theorem regret_entriesZ :
    7 - sharpZ {0, 1} = 0 ∧ 7 - sharpZ {1, 2} = 14 ∧ 7 - sharpZ {0, 2} = 4 ∧
    7 - mirrorZ {0, 1} = 14 ∧ 7 - mirrorZ {1, 2} = 0 ∧ 7 - mirrorZ {0, 2} = 4 := by decide

/-- **Repaired acquisition.**  One paid interaction measurement, the value of `{0,1}`,
identifies the world, and the resulting rule has regret `0` in both worlds. -/
theorem one_pair_query_suffices :
    sharpF (if 0 < sharpF {0, 1} then {0, 1} else {1, 2}) = 7 ∧
      mirrorF (if 0 < mirrorF {0, 1} then {0, 1} else {1, 2}) = 7 := by
  have h1 : sharpZ {0, 1} = 7 := by decide
  have h2 : mirrorZ {0, 1} = -7 := by decide
  have h3 : mirrorZ {1, 2} = 7 := by decide
  have s1 : sharpF {0, 1} = 7 := by unfold sharpF; rw [h1]; norm_num
  have m1 : mirrorF {0, 1} = -7 := by unfold mirrorF; rw [h2]; norm_num
  have m3 : mirrorF {1, 2} = 7 := by unfold mirrorF; rw [h3]; norm_num
  rw [if_pos (by rw [s1]; norm_num), if_neg (by rw [m1]; norm_num)]
  exact ⟨s1, m3⟩

end CIGAMF.P13.MarlProxyBlindness

#print axioms CIGAMF.P13.MarlProxyBlindness.mirror_local
#print axioms CIGAMF.P13.MarlProxyBlindness.worlds_agree_first_order
#print axioms CIGAMF.P13.MarlProxyBlindness.oracle_one_revision
#print axioms CIGAMF.P13.MarlProxyBlindness.proxy_rule_regret
#print axioms CIGAMF.P13.MarlProxyBlindness.proxy_mixture_regret
#print axioms CIGAMF.P13.MarlProxyBlindness.regret_entriesZ
#print axioms CIGAMF.P13.MarlProxyBlindness.one_pair_query_suffices
