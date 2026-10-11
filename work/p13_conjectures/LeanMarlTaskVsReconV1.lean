import Mathlib
import LeanMarlDecisionDepthV1

/-!
# The task floor is at most the reconstruction floor, strictly (G7, candidate L1)

Static decode model of `LeanMarlDecisionDepthV1`: a receiver with local observation `loc` decodes the senders in `D`;
sender `j` broadcasts a deterministic record `msg j F` of the world `F`; `view loc msg D F` is what it sees.
* the RECONSTRUCTION (identification) requirement: the view determines the world (`view` injective);
* the TASK requirement: some policy on the view is acceptable (`∈ safe F`) in every world.

## WHAT IS PROVED
* `identify_implies_decide` — if every world has a non-empty acceptable set and the decoded view identifies the world,
  then some policy on the view is acceptable in every world: whatever decode set suffices for reconstruction suffices for
  the task (task floor ≤ reconstruction floor).
* `task_lt_reconstruction` — strictly, on three worlds with indicator records (`indMsg`, `constLoc` of
  `LeanMarlDecisionDepthV1`): ONE decoded sender suffices for the task "name any world but the true one" (`notSelf`),
  every decode set of fewer than TWO senders makes identification (`idSafe`) impossible, and two senders suffice for it.
  So on the same channel family the task floor is 1 and the reconstruction floor is 2 = m − 1.
* The hypotheses of `identify_implies_decide` are satisfiable: they hold for `D = {0, 1}` (third conjunct of
  `task_lt_reconstruction`, proved through `identify_implies_decide`).

## WHAT THIS DOES NOT ESTABLISH
- Anything dynamic: worlds are static, records noiseless; the dynamic relay/freshness model is
  `LeanMarlReceiverFloorV1/V2` (knowledge, i.e. reconstruction-type counts), and no theorem here connects copy ages to
  decisions.
- Anything about a FIXED trained receiver (that is `LeanMarlSupportV1`, `LeanMarlFrozenFloorV1`): both requirements
  here quantify over all policies on the view.
- The general gap (one sender vs `m − 1` for every `m`) beyond `m = 3`: `LeanMarlDecisionDepthV1.decide_one_sender` and
  `identify_needs_all_but_one` give its two halves for every `m`; only the `m = 3` packaging is here.
-/

namespace CIGAMF.P13.MarlTaskVsReconV1

open Finset CIGAMF.P13.MarlDecisionDepth

/-- **Identification implies a safe decision** (given non-empty acceptable sets). -/
theorem identify_implies_decide {World Act J O M : Type*}
    [Fintype World] [DecidableEq World] [Fintype Act] [DecidableEq Act]
    [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O] [Fintype M] [DecidableEq M] [Nonempty Act]
    (safe : World → Finset Act) (loc : World → O) (msg : J → World → M) (D : Finset J)
    (hsafe : ∀ F, (safe F).Nonempty)
    (hid : ∀ F G, view loc msg D F = view loc msg D G → F = G) :
    ∃ pol : O × (J → Option M) → Act, ∀ F, pol (view loc msg D F) ∈ safe F := by
  classical
  choose a ha using hsafe
  refine ⟨fun v => if hv : ∃ G, view loc msg D G = v then a hv.choose else Classical.arbitrary Act, fun F => ?_⟩
  have hex : ∃ G, view loc msg D G = view loc msg D F := ⟨F, rfl⟩
  dsimp only
  rw [dite_eq_left hex]
  show a hex.choose ∈ safe F
  rw [hid _ _ hex.choose_spec]
  exact ha F

/-- Two distinct senders are left out by any decode set of fewer than two of three senders. -/
theorem two_left_out : ∀ D : Finset (Fin 3), D.card < 2 → ∃ u v : Fin 3, u ≠ v ∧ u ∉ D ∧ v ∉ D := by
  intro D hD
  have hc : 1 < Dᶜ.card := by rw [Finset.card_compl, Fintype.card_fin]; omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 hc
  exact ⟨u, v, huv, Finset.mem_compl.1 hu, Finset.mem_compl.1 hv⟩

/-- The decode set `{0, 1}` identifies the world among three (indicator records). -/
theorem pair_identifies :
    ∀ F G : Fin 3, view constLoc indMsg ({0, 1} : Finset (Fin 3)) F = view constLoc indMsg ({0, 1} : Finset (Fin 3)) G →
      F = G := by
  decide

/-- **Task floor 1 < reconstruction floor 2** on three worlds. -/
theorem task_lt_reconstruction :
    -- one decoded sender suffices for the task "name any world but the true one"
    (∃ D : Finset (Fin 3), D.card = 1 ∧
        ∃ pol : Unit × (Fin 3 → Option Bool) → Fin 3, ∀ F, pol (view constLoc indMsg D F) ∈ notSelf F) ∧
    -- fewer than two decoded senders cannot identify the world
    (∀ D : Finset (Fin 3), D.card < 2 →
        ¬ ∃ pol : Unit × (Fin 3 → Option Bool) → Fin 3, ∀ F, pol (view constLoc indMsg D F) ∈ idSafe F) ∧
    -- two decoded senders identify it (the hypotheses of `identify_implies_decide` hold here)
    (∃ D : Finset (Fin 3), D.card = 2 ∧
        ∃ pol : Unit × (Fin 3 → Option Bool) → Fin 3, ∀ F, pol (view constLoc indMsg D F) ∈ idSafe F) := by
  refine ⟨⟨{⟨0, by omega⟩}, by simp, decide_one_sender (m := 3) (by norm_num)⟩, ?_, ?_⟩
  · intro D hD
    obtain ⟨u, v, huv, hu, hv⟩ := two_left_out D hD
    exact identify_needs_all_but_one D u v huv hu hv
  · refine ⟨{0, 1}, by decide, ?_⟩
    exact identify_implies_decide (idSafe (m := 3)) (constLoc (m := 3)) (indMsg (m := 3))
      ({0, 1} : Finset (Fin 3)) (fun F => ⟨F, by simp [idSafe]⟩) pair_identifies

end CIGAMF.P13.MarlTaskVsReconV1

#print axioms CIGAMF.P13.MarlTaskVsReconV1.identify_implies_decide
#print axioms CIGAMF.P13.MarlTaskVsReconV1.two_left_out
#print axioms CIGAMF.P13.MarlTaskVsReconV1.pair_identifies
#print axioms CIGAMF.P13.MarlTaskVsReconV1.task_lt_reconstruction
