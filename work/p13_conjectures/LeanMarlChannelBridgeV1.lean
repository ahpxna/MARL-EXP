import Mathlib
import LeanMarlRelayOneHopV1
import LeanMarlAgeFirstInjectionV1
import LeanMarlPrefixThresholdV1

/-!
# Bridge: the injection bound holds on the prefix channel

`LeanMarlAgeFirstInjectionV1.injection_bound` assumes the age-first head is transmitted at every step.  On the prefix
channel (threshold form, `LeanMarlRelayOneHopV1.prefixDecoded`) with every threshold at least one and at least two
agents, the sender at position `0` is decoded by every other receiver, so it is transmitted.  This module discharges
the hypothesis there.

## WHAT IS PROVED
* `head_transmitted` — with `m ≥ 2` and thresholds `≥ 1`, the sender at position `0` belongs to the transmitted set
  (the union of the decoded sets).
* `injection_bound_prefix` — on the prefix channel, if at every step the sender at position `0` is the age-first head
  (key-minimal), every sender is transmitted at least once in every `m` consecutive steps.
* `threshold_mono` — the decoding threshold `K + [pos i < K]` is monotone in the capacity `K`, so the monotonicity of
  `LeanMarlRelayMonotoneV1` holds in capacity.
* `capped_eq` — the cap rule (decoded sets restricted to the first `c` positions) keeps the threshold form with
  `min(r, c)`; hence `capped_cover_exists` and `capped_head_decoded`: the covering receiver and the decoded head, and
  so the one-step bound of `LeanMarlRelayOneHopV1`, apply under the cap (cap4 in E3).

## WHAT THIS DOES NOT ESTABLISH
- That the E3 order puts the age-first head at position `0`: that is the definition of the age-first order
  (`models/marl_delivery_music.py`), not a theorem.
-/

namespace CIGAMF.P13.MarlChannelBridge

open Finset
open CIGAMF.P13.MarlRelayOneHop
open CIGAMF.P13.MarlAgeFirstInjection

variable {m : ℕ}

/-- The transmitted set of the prefix channel. -/
def transmitted (pos r : Fin m → ℕ) : Finset (Fin m) := univ.biUnion fun i => prefixDecoded pos r i

theorem head_transmitted (hm : 2 ≤ m) (pos r : Fin m → ℕ) (hd : Fin m) (h0 : pos hd = 0) (hr : ∀ i, 1 ≤ r i) :
    hd ∈ transmitted pos r := by
  obtain ⟨i, hi⟩ : ∃ i : Fin m, i ≠ hd := by
    by_contra hall
    push_neg at hall
    have h1 : (⟨0, by omega⟩ : Fin m) = hd := hall _
    have h2 : (⟨1, by omega⟩ : Fin m) = hd := hall _
    have := congrArg Fin.val (h1.trans h2.symm)
    simp at this
  exact mem_biUnion.mpr ⟨i, mem_univ _, prefix_head_decoded pos r hd h0 hr i hi⟩

/-- **The injection bound on the prefix channel.** -/
theorem injection_bound_prefix (hm : 2 ≤ m) (pos r : ℕ → Fin m → ℕ) (hr : ∀ t i, 1 ≤ r t i) (h : ℕ → Fin m)
    (h0 : ∀ t, pos t (h t) = 0)
    (hmin : ∀ t j, j ≠ h t → key (fun t => transmitted (pos t) (r t)) t (h t) < key (fun t => transmitted (pos t) (r t)) t j)
    (t : ℕ) (j : Fin m) :
    ∃ u, t ≤ u ∧ u ≤ t + (m - 1) ∧ j ∈ transmitted (pos u) (r u) :=
  injection_bound ⟨fun t => head_transmitted hm (pos t) (r t) (h t) (h0 t) (hr t), hmin⟩ t j

/-- The decoding threshold is monotone in the capacity. -/
theorem threshold_mono (pos : Fin m → ℕ) (i : Fin m) {K K' : ℕ} (hK : K ≤ K') :
    CIGAMF.P13.MarlPrefixThreshold.threshold pos K i ≤ CIGAMF.P13.MarlPrefixThreshold.threshold pos K' i := by
  unfold CIGAMF.P13.MarlPrefixThreshold.threshold
  split_ifs <;> omega

/-- The cap rule: decoded sets restricted to the first `c` positions. -/
def capped (pos r : Fin m → ℕ) (c : ℕ) (i : Fin m) : Finset (Fin m) := (prefixDecoded pos r i).filter fun j => pos j < c

theorem capped_eq (pos r : Fin m → ℕ) (c : ℕ) (i : Fin m) :
    capped pos r c i = prefixDecoded pos (fun i => min (r i) c) i := by
  ext j
  simp only [capped, prefixDecoded, mem_filter, mem_univ, true_and, lt_min_iff]
  tauto

theorem capped_cover_exists [NeZero m] (pos r : Fin m → ℕ) (c : ℕ) :
    ∃ cv, ∀ j, (∃ i, j ∈ capped pos r c i) → j ≠ cv → j ∈ capped pos r c cv := by
  obtain ⟨cv, hcv⟩ := prefix_cover_exists pos (fun i => min (r i) c)
  exact ⟨cv, fun j ⟨i, hi⟩ hj => by rw [capped_eq] at hi ⊢; exact hcv j ⟨i, hi⟩ hj⟩

theorem capped_head_decoded (pos r : Fin m → ℕ) (c : ℕ) (hc : 1 ≤ c) (hd : Fin m) (h0 : pos hd = 0)
    (hr : ∀ i, 1 ≤ r i) : ∀ i, i ≠ hd → hd ∈ capped pos r c i := by
  intro i hi
  rw [capped_eq]
  exact prefix_head_decoded pos (fun i => min (r i) c) hd h0 (fun i => le_min (hr i) hc) i hi

end CIGAMF.P13.MarlChannelBridge

#print axioms CIGAMF.P13.MarlChannelBridge.head_transmitted
#print axioms CIGAMF.P13.MarlChannelBridge.injection_bound_prefix
#print axioms CIGAMF.P13.MarlChannelBridge.threshold_mono
#print axioms CIGAMF.P13.MarlChannelBridge.capped_eq
#print axioms CIGAMF.P13.MarlChannelBridge.capped_cover_exists
#print axioms CIGAMF.P13.MarlChannelBridge.capped_head_decoded
