import Mathlib

/-!
# Imitating a privileged teacher is not monotone in the student's information (while the Bayes risk is)

E3 context (ledger L-213/L-214, 01/10/2026): a relay student whose input CONTAINS the zero-byte student's input (so it can
represent that policy by ignoring every message) still loses to it at constant capacity K = 1.  `bayes_refine`
(LeanMarlCommValueV1) says a finer view never has larger Bayes risk; the students, however, are trained to IMITATE a
privileged teacher (DAgger, cross-entropy to the teacher's action), whose population optimum is the per-class
MAXIMUM-AGREEMENT policy.  This module shows on a three-world instance that this objective is not information-monotone.

Instance: worlds 0, 1, 2 with law 1/2, 3/10, 1/5; two actions; teacher actions 0, 1, 0; acceptable sets {0}, {0, 1}, {0}
(the teacher's own action is always acceptable, as in the E3 sets A_ε); coarse view: nothing; fine view: {0} | {1, 2}.

## WHAT IS PROVED
* `fine_refines` — the fine view refines the coarse one; `teacher_safe` — the teacher is always acceptable.
* `polC_maxAgree`, `polF_maxAgree` — `polC` (always 0) and `polF` (0 on {0}, 1 on {1, 2}) are maximum-agreement policies of
  the coarse and the fine view: the population optima of imitation on each view.
* `agreement_rises` — refining raises the teacher agreement of the imitation optimum (7/10 → 4/5) …
* `imitation_risk_rises` — … and raises its unacceptable mass (0 → 1/5): more information, worse decisions.
* `bayes_unchanged` — on the same fine view the policy "always 0" has unacceptable mass 0, so the Bayes risk did not rise
  (as `bayes_refine` requires): the loss comes from the objective, not from the information.

## WHAT THIS DOES NOT ESTABLISH
- That the E3 K = 1 loss is caused by this mechanism: the iid-trained relay student is LESS acceptable than Z at K = 1
  (0.848 vs 0.874), i.e. it fails even at agreement there (an extrapolation failure); this instance explains a possible
  residual where agreement is matched or higher and return is not (age clip: 0.878 vs 0.874, return −0.89 %).
- Anything about closed-loop return, finite data or optimisation: the statements are about population optima of one
  decision.
-/

namespace CIGAMF.P13.MarlImitationGap

open Finset

/-- The law on the three worlds. -/
def p : Fin 3 → ℚ := ![1/2, 3/10, 1/5]
/-- The privileged teacher's action in each world. -/
def aT : Fin 3 → Fin 2 := ![0, 1, 0]
/-- Acceptable actions (the teacher's own action is always one of them). -/
def safe : Fin 3 → Finset (Fin 2) := ![{0}, {0, 1}, {0}]
/-- The zero-information view. -/
def coarse : Fin 3 → Fin 1 := fun _ => 0
/-- The finer view: world 0 alone, worlds 1 and 2 together. -/
def fine : Fin 3 → Fin 2 := ![0, 1, 1]

/-- Teacher-agreement mass of action `a` in the class `o` of a view. -/
def agree {O : Type*} [DecidableEq O] (obs : Fin 3 → O) (o : O) (a : Fin 2) : ℚ :=
  ∑ w, if obs w = o ∧ aT w = a then p w else 0

/-- Total teacher agreement of a deterministic policy on a view. -/
def agreement {O : Type*} (obs : Fin 3 → O) (pol : O → Fin 2) : ℚ :=
  ∑ w, if pol (obs w) = aT w then p w else 0

/-- Unacceptable mass of a deterministic policy on a view (the risk of LeanMarlCommValueV1 for a deterministic policy). -/
def unsafeMass {O : Type*} (obs : Fin 3 → O) (pol : O → Fin 2) : ℚ :=
  ∑ w, if pol (obs w) ∉ safe w then p w else 0

/-- Imitation optimum on the coarse view. -/
def polC : Fin 1 → Fin 2 := fun _ => 0
/-- Imitation optimum on the fine view. -/
def polF : Fin 2 → Fin 2 := ![0, 1]
/-- A fine-view policy that ignores the extra information. -/
def polB : Fin 2 → Fin 2 := fun _ => 0

theorem fine_refines : ∀ w v : Fin 3, fine w = fine v → coarse w = coarse v := fun _ _ _ => rfl

theorem teacher_safe : ∀ w : Fin 3, aT w ∈ safe w := by decide

theorem polC_maxAgree : ∀ (o : Fin 1) (a : Fin 2), agree coarse o a ≤ agree coarse o (polC o) := by
  intro o a
  fin_cases o; fin_cases a <;> simp [agree, coarse, polC, aT, p, Fin.sum_univ_three] <;> norm_num

theorem polF_maxAgree : ∀ (o : Fin 2) (a : Fin 2), agree fine o a ≤ agree fine o (polF o) := by
  intro o a
  fin_cases o <;> fin_cases a <;> simp [agree, fine, polF, aT, p, Fin.sum_univ_three] <;> norm_num

theorem agreement_rises : agreement coarse polC = 7/10 ∧ agreement fine polF = 4/5 := by
  constructor <;> simp [agreement, coarse, fine, polC, polF, aT, p, Fin.sum_univ_three] <;> norm_num

theorem imitation_risk_rises : unsafeMass coarse polC = 0 ∧ unsafeMass fine polF = 1/5 := by
  constructor <;> simp [unsafeMass, coarse, fine, polC, polF, safe, p, Fin.sum_univ_three] <;> norm_num

theorem bayes_unchanged : unsafeMass fine polB = 0 := by
  simp [unsafeMass, fine, polB, safe, p, Fin.sum_univ_three]

/-- **Imitation is not information-monotone.**  On a view that refines the zero-information view, the population optimum
of teacher imitation agrees MORE with the teacher and is unacceptable MORE often, while a policy on the same refined view
that ignores the extra information keeps the coarse risk. -/
theorem imitation_gap :
    (∀ w v, fine w = fine v → coarse w = coarse v) ∧ (∀ w, aT w ∈ safe w) ∧
    (∀ o a, agree coarse o a ≤ agree coarse o (polC o)) ∧ (∀ o a, agree fine o a ≤ agree fine o (polF o)) ∧
    agreement coarse polC < agreement fine polF ∧ unsafeMass coarse polC < unsafeMass fine polF ∧
    unsafeMass fine polB = unsafeMass coarse polC := by
  refine ⟨fine_refines, teacher_safe, polC_maxAgree, polF_maxAgree, ?_, ?_, ?_⟩
  · rw [agreement_rises.1, agreement_rises.2]; norm_num
  · rw [imitation_risk_rises.1, imitation_risk_rises.2]; norm_num
  · rw [bayes_unchanged, imitation_risk_rises.1]

end CIGAMF.P13.MarlImitationGap

#print axioms CIGAMF.P13.MarlImitationGap.imitation_gap
