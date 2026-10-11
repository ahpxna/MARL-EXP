import Mathlib
import LeanMarlPrefixInstanceV1

/-!
# Upgrades can always be emulated, downgrades cannot: the direction asymmetry of channel repair

PROTOCOL_E3_AGE_REMAP_20261002 / MARL_DIRECTION_ROUND10_20261002 (02/10/2026 12:0x EDT).  A learned receiver tolerates
the exposures it was trained on.  If the deployment channel is RICHER than the training channel (an upgrade), the network
(or the receiver itself) can reproduce the training channel exactly — decode only the training budget's packets of the same
committed order — so the training exposure stays achievable.  If it is POORER (a downgrade), the receiver floor forbids it.
In the window-knowledge model of `LeanMarlReceiverFloorV2` (full relay, unbounded memory):

## WHAT IS PROVED
* `know_mono` — more decoding never loses knowledge: decode sets pointwise included ⇒ knowledge included, at every step.
* `prefix_decode_mono` — in the prefix channel with the same committed orders, budgets `K ≤ K'` give decode sets
  `D_K r ⊆ D_K' r` for every receiver and step.
* `upgrade_emulation` — for every scheduler and every budget sequence `K ≤ K'`, the budget-`K` channel is obtained from the
  budget-`K'` channel by decoding a SUBSET of each receiver's packets (`K` of its `K'`), so every knowledge process of the
  `K` channel is realised under `K'` (exactly, by throttling) and is dominated by the full use of `K'` (`know_mono`).
* `downgrade_strict` — the converse fails: three agents, budget 2 lets receiver 2 know both other senders after one step,
  while under budget 1 NO scheduler lets any receiver know more than one (the floor) — a fresher exposure of the richer
  channel that the poorer channel cannot produce.

## WHAT THIS DOES NOT ESTABLISH
- Anything about the learned receiver's value (empirical: P-UP2, E1, L-249 / L-258); the emulated channel recovers the
  training EXPOSURE, i.e. the receiver's training-channel performance, not more.
- Interface-level remaps (relabelling ages) — those are evaluated empirically (PROTOCOL_E3_AGE_REMAP_20261002).
-/

namespace CIGAMF.P13.MarlEmulationV1

open Finset CIGAMF.P13.MarlReceiverFloorV2 CIGAMF.P13.MarlPrefixInstanceV1

variable {α : Type*} [DecidableEq α]

/-- **More decoding never loses knowledge.** -/
theorem know_mono (sch sch' : ℕ → Step α) (hD : ∀ s r, (sch s).D r ⊆ (sch' s).D r) :
    ∀ n r, know sch n r ⊆ know sch' n r := by
  intro n
  induction n with
  | zero => intro r; simp [know]
  | succ n ih =>
    intro r x hx
    simp only [know, mem_union, mem_biUnion, mem_insert] at hx ⊢
    rcases hx with hx | ⟨o, ho, hxo⟩
    · exact Or.inl (ih r hx)
    · refine Or.inr ⟨o, hD n r ho, ?_⟩
      rcases hxo with rfl | hxo
      · exact Or.inl rfl
      · exact Or.inr (ih o hxo)

/-- Prefix channel, same orders: a smaller budget decodes a subset. -/
theorem prefix_decode_mono (l : List α) (K K' : α → ℕ) (Kst Kst' : ℕ) (hK : ∀ r, K r ≤ Kst) (hK' : ∀ r, K' r ≤ Kst')
    (d : α) (hle : ∀ r, K r ≤ K' r) (r : α) :
    (prefixStep l K Kst hK d).D r ⊆ (prefixStep l K' Kst' hK' d).D r := by
  intro x hx
  simp only [prefixStep, List.mem_toFinset] at hx ⊢
  exact mem_take_mono (hle r) hx

/-- **Upgrade emulation.**  For every scheduler (orders `ord`) and budgets `Kb ≤ Kb'`, receivers of the budget-`Kb'` channel
that decode only the budget-`Kb` subset reproduce the budget-`Kb` channel exactly (its decode sets are subsets of the
richer ones), and the richer channel used fully dominates it. -/
theorem upgrade_emulation (ord : ℕ → List α) (Kb Kb' : ℕ → α → ℕ) (Kst Kst' : ℕ → ℕ) (hK : ∀ s r, Kb s r ≤ Kst s)
    (hK' : ∀ s r, Kb' s r ≤ Kst' s) (d : α) (hle : ∀ s r, Kb s r ≤ Kb' s r) :
    (∀ s r, (prefixStep (ord s) (Kb s) (Kst s) (hK s) d).D r ⊆ (prefixStep (ord s) (Kb' s) (Kst' s) (hK' s) d).D r) ∧
    ∀ n r, know (fun s => prefixStep (ord s) (Kb s) (Kst s) (hK s) d) n r ⊆
      know (fun s => prefixStep (ord s) (Kb' s) (Kst' s) (hK' s) d) n r := by
  have hD : ∀ s r, (prefixStep (ord s) (Kb s) (Kst s) (hK s) d).D r ⊆ (prefixStep (ord s) (Kb' s) (Kst' s) (hK' s) d).D r :=
    fun s r => prefix_decode_mono _ _ _ _ _ _ _ _ (hle s) r
  exact ⟨hD, know_mono _ _ hD⟩

/-- The richer channel of the witness: three agents, every budget 2, order `[0, 1, 2]`. -/
def richSch : ℕ → Step (Fin 3) := fun _ => prefixStep [0, 1, 2] (fun _ => 2) 2 (fun _ => le_rfl) 0

/-- **Downgrades are not emulable.**  Under budget 2 receiver 2 knows both other senders after one step; under budget 1
no scheduler (any orders) lets any receiver know more than one other sender after one step. -/
theorem downgrade_strict :
    ((know richSch 1 (2 : Fin 3)).erase 2).card = 2 ∧
    ∀ (ord : ℕ → List (Fin 3)) (i : Fin 3),
      ((know (fun s => prefixStep (ord s) (fun _ => 1) 1 (fun _ => le_rfl) 0) 1 i).erase i).card ≤ 1 := by
  refine ⟨by decide, fun ord i => ?_⟩
  have h := prefix_receiver_floor ord (fun _ _ => 1) (fun _ => 1) (fun _ _ => le_rfl) 0 1 i
  simpa using h

end CIGAMF.P13.MarlEmulationV1

#print axioms CIGAMF.P13.MarlEmulationV1.know_mono
#print axioms CIGAMF.P13.MarlEmulationV1.prefix_decode_mono
#print axioms CIGAMF.P13.MarlEmulationV1.upgrade_emulation
#print axioms CIGAMF.P13.MarlEmulationV1.downgrade_strict
