import Mathlib

/-!
# Training risk certifies nothing outside the training age support: why an upgrade can hurt

Ledger L-250 (P-UP2, 5/5 seeds) and L-249 (E1 ML2): a receiver trained at constant K = 1 (relayed copies 1–8 steps old) loses
most of its advantage over compiled silence when the channel IMPROVES (iid: copies 0–2 steps old).  This file isolates the
mathematical reason in a finite model: the training risk of a rule depends only on its values on the support of the training
distribution, so two rules that are equally optimal in training can behave arbitrarily differently on ages never trained on.

## WHAT IS PROVED
* `risk_eq_of_agree_on_support` — if two rules agree wherever the training weights are non-zero, their training risks are
  equal (any loss, any finite input space).
* `upgrade_hazard` — an explicit instance (message bit × age ∈ {fresh, one step old}; a one-step-old copy reports the
  OPPOSITE of the current state, as for an oscillating process): trained on old copies only, the age-aware rule `f` and the
  age-blind rule `g` both have training risk 0 (both optimal); on a FRESHER deployment (fresh copies only) `f` has risk 0
  while `g` has risk 1, worse than the silent rule's 1/2.  So training optimality on the poorer channel does not prevent a
  loss below silence on the better one.
* `hazard_meets_w1_bound` — the instance is exactly the boundary of `LeanMarlMismatchW1V1.lipschitz_w1_bound`: `g`'s
  per-age risk changes by 1 between consecutive ages (L = 1), the deployment and training age histograms are at W1 = 1, and
  the risk moves by exactly 1 = L · W1.  A smoothness assumption across ages is therefore what any transfer guarantee needs.

## WHAT THIS DOES NOT ESTABLISH
- That the trained CityFlow receivers behave like `g` (the age-response probes, L-237, are the empirical evidence).
-/

namespace CIGAMF.P13.MarlSupportV1

open Finset

/-- Training risk of a rule: Σ_x P x · loss x (rule x). -/
def risk {X Y : Type*} [Fintype X] (P : X → ℝ) (loss : X → Y → ℝ) (r : X → Y) : ℝ := ∑ x, P x * loss x (r x)

theorem risk_eq_of_agree_on_support {X Y : Type*} [Fintype X] (P : X → ℝ) (loss : X → Y → ℝ) (f g : X → Y)
    (h : ∀ x, P x ≠ 0 → f x = g x) : risk P loss f = risk P loss g := by
  unfold risk
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : P x = 0
  · simp [hx]
  · rw [h x hx]

/-- Inputs: (message bit m, age a) with a = 0 fresh, a = 1 one step old.  The current state is m when fresh and 1 − m when
one step old (an oscillating process).  Loss 0-1 on the action vs the current state. -/
def state (x : Fin 2 × Fin 2) : Fin 2 := if x.2 = 0 then x.1 else 1 - x.1
def loss01 (x : Fin 2 × Fin 2) (y : Fin 2) : ℝ := if y = state x then 0 else 1
/-- training: uniform message, old copies only (the poorer channel) -/
noncomputable def Ptrain (x : Fin 2 × Fin 2) : ℝ := if x.2 = 1 then 1 / 2 else 0
/-- deployment after the upgrade: uniform message, fresh copies only -/
noncomputable def Qdeploy (x : Fin 2 × Fin 2) : ℝ := if x.2 = 0 then 1 / 2 else 0
/-- age-aware rule -/
def f (x : Fin 2 × Fin 2) : Fin 2 := state x
/-- age-blind rule (learned "the copy reports the opposite", the only thing training showed) -/
def g (x : Fin 2 × Fin 2) : Fin 2 := 1 - x.1
/-- silent rule (ignores the message) -/
def silent (_ : Fin 2 × Fin 2) : Fin 2 := 0

theorem upgrade_hazard :
    risk Ptrain loss01 f = 0 ∧ risk Ptrain loss01 g = 0 ∧
    (∀ r : Fin 2 × Fin 2 → Fin 2, 0 ≤ risk Ptrain loss01 r) ∧
    risk Qdeploy loss01 f = 0 ∧ risk Qdeploy loss01 g = 1 ∧ risk Qdeploy loss01 silent = 1 / 2 := by
  refine ⟨?_, ?_, fun r => ?_, ?_, ?_, ?_⟩
  · norm_num [risk, Ptrain, loss01, f, Fintype.sum_prod_type, Fin.sum_univ_two]
  · norm_num [risk, Ptrain, loss01, g, state, Fintype.sum_prod_type, Fin.sum_univ_two]
  · unfold risk
    refine sum_nonneg fun x _ => mul_nonneg ?_ ?_
    · unfold Ptrain; split_ifs <;> norm_num
    · unfold loss01; split_ifs <;> norm_num
  · norm_num [risk, Qdeploy, loss01, f, Fintype.sum_prod_type, Fin.sum_univ_two]
  · norm_num [risk, Qdeploy, loss01, g, state, Fintype.sum_prod_type, Fin.sum_univ_two]
  · norm_num [risk, Qdeploy, loss01, silent, state, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- `g`'s risk restricted to age a (uniform message): 1 at a = 0, 0 at a = 1 — a 1-Lipschitz age response; the age
histograms δ₀ (deployment) and δ₁ (training) are at W1 = 1; the risk moves by exactly 1 = L · W1. -/
theorem hazard_meets_w1_bound :
    (∑ m : Fin 2, (1 / 2 : ℝ) * loss01 (m, 0) (g (m, 0))) = 1 ∧
    (∑ m : Fin 2, (1 / 2 : ℝ) * loss01 (m, 1) (g (m, 1))) = 0 ∧
    risk Qdeploy loss01 g - risk Ptrain loss01 g = 1 * 1 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [loss01, g, state, Fin.sum_univ_two]
  · norm_num [loss01, g, state, Fin.sum_univ_two]
  · have h := upgrade_hazard
    rw [h.2.2.2.2.1, h.2.1]; norm_num

end CIGAMF.P13.MarlSupportV1

#print axioms CIGAMF.P13.MarlSupportV1.risk_eq_of_agree_on_support
#print axioms CIGAMF.P13.MarlSupportV1.upgrade_hazard
#print axioms CIGAMF.P13.MarlSupportV1.hazard_meets_w1_bound
