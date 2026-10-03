import Mathlib
import LeanMarlSupportV1

/-!
# Projection, not transport: matching the deployment distribution to the training one moves in-support inputs

Ledger L-266 / L-268 (02/10/2026): relabelling the ages of the deployment views by the exact monotone transport onto the
training age histogram (W1 → 0) put both CityFlow receivers below compiled silence (−4 … −7 %), while the clip — which only
moves the out-of-support ages to the edge of the support — helped (+0.69 %); in the remote-inference testbed minimal
emulation beat full emulation (L-263).  This file proves why transport is the wrong target for an interface repair.

## WHAT IS PROVED
* `push_of_fix` — a map that fixes every input of positive weight pushes the distribution onto itself.
* `transport_moves_support` — hence ANY map that pushes a deployment distribution `p` onto a different training
  distribution `q` must move some input of positive deployment weight — even when every deployment input already lies in the
  training support (the upgrade case: every iid age 0–2 is a K = 1 training age).  A projection onto the support never moves
  an in-support input (`risk_proj_eq`: the receiver's risk is unchanged on the inputs it was trained on).
* `transport_harms_optimal` — and moving in-support inputs can turn an OPTIMAL receiver below silence: in the model of
  `LeanMarlSupportV1` (message bit × age, a one-step-old copy reports the opposite state) the age-aware rule `f` has risk 0
  on fresh deployment copies; transporting them to the "old copies" training marginal (relabel age 0 → 1) gives risk 1, worse
  than the silent rule's 1/2, while the projection (the identity, every input being in support) keeps risk 0.

## WHAT THIS DOES NOT ESTABLISH
- That the clip / onefresh projections are the best interface repairs, or that a projection always helps (it only never
  changes in-support inputs; out-of-support inputs it moves can still be mishandled).
-/

namespace CIGAMF.P13.MarlProjectionV1

open Finset CIGAMF.P13.MarlSupportV1

/-- Push-forward of input weights along a map. -/
def push {X : Type*} [Fintype X] [DecidableEq X] (T : X → X) (p : X → ℝ) (y : X) : ℝ :=
  ∑ x ∈ univ.filter (fun x => T x = y), p x

theorem push_of_fix {X : Type*} [Fintype X] [DecidableEq X] (T : X → X) (p : X → ℝ) (h : ∀ x, p x ≠ 0 → T x = x) :
    push T p = p := by
  funext y
  unfold push
  rw [Finset.sum_eq_single y]
  · intro b hb hby
    by_contra hpb
    have hTb := h b hpb
    rw [mem_filter] at hb
    exact hby (hTb.symm.trans hb.2)
  · intro hy
    by_contra hpy
    exact hy (mem_filter.2 ⟨mem_univ _, h y hpy⟩)

theorem transport_moves_support {X : Type*} [Fintype X] [DecidableEq X] (T : X → X) (p q : X → ℝ)
    (hT : push T p = q) (hpq : p ≠ q) : ∃ x, p x ≠ 0 ∧ T x ≠ x := by
  by_contra hc
  push_neg at hc
  exact hpq ((push_of_fix T p hc).symm.trans hT)

/-- A projection that fixes the inputs the receiver was trained on leaves its risk on them unchanged. -/
theorem risk_proj_eq {X Y : Type*} [Fintype X] (P : X → ℝ) (loss : X → Y → ℝ) (r : X → Y) (proj : X → X)
    (hfix : ∀ x, P x ≠ 0 → proj x = x) : risk P loss (fun x => r (proj x)) = risk P loss r :=
  risk_eq_of_agree_on_support P loss _ _ fun x hx => by simp [hfix x hx]

/-- Transport of fresh copies onto the "old copies" marginal: relabel every age to 1. -/
def relabelOld (x : Fin 2 × Fin 2) : Fin 2 × Fin 2 := (x.1, 1)

theorem transport_harms_optimal :
    push relabelOld Qdeploy = Ptrain ∧
    risk Qdeploy loss01 (fun x => f (relabelOld x)) = 1 ∧
    risk Qdeploy loss01 f = 0 ∧ risk Qdeploy loss01 silent = 1 / 2 := by
  refine ⟨?_, ?_, (upgrade_hazard).2.2.2.1, (upgrade_hazard).2.2.2.2.2⟩
  · funext y
    rcases y with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;>
      norm_num [push, relabelOld, Qdeploy, Ptrain, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two]
  · norm_num [risk, Qdeploy, loss01, f, relabelOld, state, Fintype.sum_prod_type, Fin.sum_univ_two]

end CIGAMF.P13.MarlProjectionV1

#print axioms CIGAMF.P13.MarlProjectionV1.push_of_fix
#print axioms CIGAMF.P13.MarlProjectionV1.transport_moves_support
#print axioms CIGAMF.P13.MarlProjectionV1.risk_proj_eq
#print axioms CIGAMF.P13.MarlProjectionV1.transport_harms_optimal
