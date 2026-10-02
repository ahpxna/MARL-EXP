import Mathlib
import LeanMarlDecisionDepthV1

/-!
# Revision after the capacity is revealed: `R` exchanges close the price of nesting when the hitting number is `≤ R`

A broadcast commits to an order before the receivers' capacities are revealed; a receiver of capacity `K` then decodes a
prefix `D` with `|D| = K`.  With a REVISION allowance `R` (Paper 1's revision budget; Paper C's recourse), it may
exchange up to `R` decoded senders for others, keeping `|D'| ≤ |D|`.

## WHAT IS PROVED
* `revise_to_hit` — if a set `Hit` with `|Hit| ≤ |D|` and `|Hit| ≤ R` exists, some `D'` with `|D'| ≤ |D|`, at most `R`
  senders of `D` dropped (`|D \ D'| ≤ R`), contains `Hit`.
* `revision_serves` — so, by `LeanMarlDecisionDepthV1.decode_safe_iff`, if `Hit` splits every local obstruction of the
  receiver (its HITTING NUMBER is at most `R`) and its capacity is at least `|Hit|`, `R` exchanges after the reveal make
  it acceptable in every world, WHATEVER the committed order.
* `one_revision_closes_nesting` — on the two-receiver witness of `LeanMarlDecisionDepthV1` (capacities 1 and 2, where no
  nested pair serves both), the committed order `0, 1, 2` with ONE exchange for the capacity-2 receiver serves both.

## WHAT THIS DOES NOT ESTABLISH
- That a learned receiver can identify its hitting set at run time; the V-D probe (`scripts/MARL_e3_decision_depth_probe_v2.py`)
  only MEASURES the hitting number of a teacher-defined acceptable set.
- Anything about the revision channel's own cost (who learns the capacity, when).
-/

namespace CIGAMF.P13.MarlRevisionDepth

open Finset
open CIGAMF.P13.UnifiedObstructionOrder CIGAMF.P13.MarlDecisionDepth

variable {World Act J O M : Type*}
  [Fintype World] [DecidableEq World] [Fintype Act] [DecidableEq Act]
  [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O] [Fintype M] [DecidableEq M]

/-- **Exchanging at most `R` senders reaches any set of size `≤ min(|D|, R)`.** -/
theorem revise_to_hit (D Hit : Finset J) (R : ℕ) (hcap : Hit.card ≤ D.card) (hR : Hit.card ≤ R) :
    ∃ D' : Finset J, Hit ⊆ D' ∧ D'.card ≤ D.card ∧ (D \ D').card ≤ R := by
  -- keep `|D| - |Hit|` senders of `D \ Hit`, add `Hit`
  have hle : D.card - Hit.card ≤ (D \ Hit).card := by
    have h1 : (D \ Hit).card + (D ∩ Hit).card = D.card := card_sdiff_add_card_inter D Hit
    have h2 : (D ∩ Hit).card ≤ Hit.card := card_le_card inter_subset_right
    omega
  obtain ⟨E, hE, hEc⟩ := Finset.exists_subset_card_eq hle
  refine ⟨Hit ∪ E, subset_union_left, ?_, ?_⟩
  · calc (Hit ∪ E).card ≤ Hit.card + E.card := card_union_le _ _
      _ = D.card := by omega
  · -- what is dropped lies in `D \ Hit` minus `E`
    have hsub : D \ (Hit ∪ E) ⊆ (D \ Hit) \ E := by
      intro x hx
      simp only [mem_sdiff, mem_union, not_or] at hx ⊢
      exact ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩
    have hcard : ((D \ Hit) \ E).card = (D \ Hit).card - E.card := card_sdiff_of_subset hE
    have h1 : (D \ Hit).card + (D ∩ Hit).card = D.card := card_sdiff_add_card_inter D Hit
    have := card_le_card hsub
    have h3 : (D ∩ Hit).card ≤ Hit.card := card_le_card inter_subset_right
    omega

/-- **`R` exchanges serve any receiver whose hitting number is at most `R` and whose capacity covers it.** -/
theorem revision_serves [Nonempty Act] (safe : World → Finset Act) (loc : World → O) (msg : J → World → M)
    (D Hit : Finset J) (R : ℕ) (hcap : Hit.card ≤ D.card) (hR : Hit.card ≤ R)
    (hhit : ∀ H : Finset World, LocalObstruction safe loc H → Splits msg Hit H) :
    ∃ D' : Finset J, D'.card ≤ D.card ∧ (D \ D').card ≤ R ∧
      ∃ pol : O × (J → Option M) → Act, ∀ F, pol (view loc msg D' F) ∈ safe F := by
  obtain ⟨D', hHD, hc, hd⟩ := revise_to_hit D Hit R hcap hR
  refine ⟨D', hc, hd, ?_⟩
  rw [decode_safe_iff]
  exact fun H hH => splits_mono msg hHD (hhit H hH)

/-- **One exchange closes the nesting price of the two-receiver witness.**  Committed order `0, 1, 2`: receiver 1
(capacity 1) decodes `{0}` and is served; receiver 2 (capacity 2) decodes `{0, 1}`, exchanges `0` for `2`, and is
served; neither needs a second exchange. -/
theorem one_revision_closes_nesting :
    (∃ pol : Unit × (Fin 3 → Option Bool) → Bool × Bool,
      ∀ F, pol (view noLoc bitMsg ({0} : Finset (Fin 3)) F) ∈ safe1 F) ∧
    ∃ D' : Finset (Fin 3), D'.card ≤ ({0, 1} : Finset (Fin 3)).card ∧
      (({0, 1} : Finset (Fin 3)) \ D').card ≤ 1 ∧
      ∃ pol : Unit × (Fin 3 → Option Bool) → Bool × Bool, ∀ F, pol (view noLoc bitMsg D' F) ∈ safe2 F := by
  obtain ⟨h1, h2⟩ := nesting_price_individual
  refine ⟨h1, ⟨{1, 2}, by decide, by decide, h2⟩⟩

end CIGAMF.P13.MarlRevisionDepth

#print axioms CIGAMF.P13.MarlRevisionDepth.revise_to_hit
#print axioms CIGAMF.P13.MarlRevisionDepth.revision_serves
#print axioms CIGAMF.P13.MarlRevisionDepth.one_revision_closes_nesting
