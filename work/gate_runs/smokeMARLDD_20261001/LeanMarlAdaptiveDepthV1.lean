import Mathlib
import LeanMarlDecisionDepthV1
import «LeanPaperBDecisionOrderV1»

/-!
# Anytime decoding of a prefix broadcast: paper B's per-world decision order

A receiver may decode the broadcast in its order and STOP as soon as its current view admits an action acceptable in
every world consistent with it.  At world `w` it then stops at paper B's decision order `dOrder w`
(`LeanPaperBDecisionOrderV1`), read on the broadcast with one "query" (the stream itself) whose separation order is
`sepPos` of `LeanMarlDecisionDepthV1`.

## WHAT IS PROVED
* `sepPos_symm`, `sepPos_ultrametric` — the broadcast's separation order is symmetric and ULTRAMETRIC (a sender that
  splits `u, v` splits `x` from one of them), whenever every position is below the "never" value `T`.
* `near_iff_view` — for capacities `s < T`, paper B's `near w s` (the worlds the observer cannot tell from `w` at order
  `s`) is exactly `w`'s view class at capacity `s`: `l ∈ near w s ↔ view (prefixD pos s) l = view (prefixD pos s) w`.
* `anytime_stop_iff` — so a receiver at world `w` can stop at capacity `s < T` iff `CommonSafe` holds on its view class,
  and `dOrder w` is the anytime decoder's stopping capacity (whenever the class at `dOrder w` is reached below `T`).
* `worst_anytime_depth_iff` — **the worst case is the fixed depth**: by B's `max_order_iff` (needs the ultrametric
  property, proved here), some world needs anytime depth `≥ s` iff some obstruction has every pair separated only at
  positions `≥ s − 1`.  Adaptivity gains nothing in the worst case; it can only gain on average over worlds.

## WHAT THIS DOES NOT ESTABLISH
- The stopping rule uses the model's acceptable sets; a learned receiver does not know them (the V-D probe measures a
  teacher's own stopping depth as a labelled diagnostic).
- Noise: with noisy records `decision_upper`/`decision_lower` of paper B give the per-world characteristic game of order
  `h^{2 dOrder w}`; not re-instantiated here.
-/

namespace CIGAMF.P13.MarlAdaptiveDepth

open Finset
open CIGAMF.P13.UnifiedObstructionOrder CIGAMF.P13.MarlDecisionDepth
open CIGAMF.P13.PaperBSafe CIGAMF.P13.PaperBDecisionOrder

variable {World Act J O M : Type*}
  [Fintype World] [DecidableEq World] [Fintype Act] [DecidableEq Act]
  [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O] [Fintype M] [DecidableEq M]

variable (loc : World → O) (msg : J → World → M) (pos : J → ℕ) (T : ℕ)

theorem sepPos_zero {F G : World} (h : loc F ≠ loc G) : sepPos loc msg pos T F G = 0 := by
  unfold sepPos; rw [if_pos h]

theorem sepPos_le_of_diff {F G : World} (hl : loc F = loc G) {j : J} (hj : msg j F ≠ msg j G) :
    sepPos loc msg pos T F G ≤ pos j + 1 := by
  unfold sepPos
  rw [if_neg (not_not.mpr hl)]
  have hmem : j ∈ univ.filter (fun j => msg j F ≠ msg j G) := by simpa using hj
  rw [dif_pos ⟨j, hmem⟩]
  exact Finset.inf'_le _ hmem

theorem sepPos_le_T (hT : ∀ j, pos j < T) (F G : World) : sepPos loc msg pos T F G ≤ T := by
  unfold sepPos
  split_ifs with h1 h2
  · exact Nat.zero_le _
  · obtain ⟨j, hj⟩ := h2
    exact (Finset.inf'_le _ hj).trans (by have := hT j; omega)
  · exact le_rfl

theorem sepPos_symm (F G : World) : sepPos loc msg pos T F G = sepPos loc msg pos T G F := by
  have hfil : (univ.filter fun j => msg j F ≠ msg j G) = univ.filter fun j => msg j G ≠ msg j F := by
    ext j; simp [ne_comm]
  unfold sepPos
  by_cases h : loc F = loc G
  · rw [if_neg (not_not.mpr h), if_neg (not_not.mpr h.symm)]
    simp only [hfil]
  · rw [if_pos h, if_pos (Ne.symm h)]

/-- **The broadcast's separation order is ultrametric.** -/
theorem sepPos_ultrametric (hT : ∀ j, pos j < T) (u v x : World) :
    min (sepPos loc msg pos T u x) (sepPos loc msg pos T x v) ≤ sepPos loc msg pos T u v := by
  by_cases hl : loc u = loc v
  · by_cases hs : (univ.filter (fun j => msg j u ≠ msg j v)).Nonempty
    · obtain ⟨j, hj, hje⟩ := Finset.exists_mem_eq_inf' hs (fun j => pos j + 1)
      have huv : sepPos loc msg pos T u v = pos j + 1 := by
        unfold sepPos; rw [if_neg (not_not.mpr hl), dif_pos hs, hje]
      rw [huv]
      have hj' : msg j u ≠ msg j v := by simpa using hj
      by_cases hlx : loc u = loc x
      · by_cases hux : msg j u = msg j x
        · have hxv : msg j x ≠ msg j v := fun e => hj' (hux.trans e)
          have := sepPos_le_of_diff loc msg pos T (hlx.symm.trans hl) hxv
          omega
        · have := sepPos_le_of_diff loc msg pos T hlx hux
          omega
      · rw [sepPos_zero loc msg pos T hlx]; omega
    · have huv : sepPos loc msg pos T u v = T := by
        unfold sepPos; rw [if_neg (not_not.mpr hl), dif_neg hs]
      rw [huv]
      exact (min_le_left _ _).trans (sepPos_le_T loc msg pos T hT u x)
  · by_cases hlx : loc u = loc x
    · have hxv : loc x ≠ loc v := fun e => hl (hlx.trans e)
      rw [sepPos_zero loc msg pos T hxv]; omega
    · rw [sepPos_zero loc msg pos T hlx]; omega

/-- The broadcast as a one-query channel of paper B. -/
noncomputable def sqB : Unit → World → World → ℕ := fun _ => sepPos loc msg pos T

theorem sepQ_sqB (u v : World) : sepQ (sqB loc msg pos T) u v = sepPos loc msg pos T u v := by
  unfold sepQ sqB
  exact le_antisymm (Finset.inf'_le _ (mem_univ ())) (Finset.le_inf' _ _ fun _ _ => le_rfl)

/-- **Paper B's `near` is the view class.** -/
theorem near_iff_view (s : ℕ) (hsT : s < T) (w l : World) :
    l ∈ near (sqB loc msg pos T) w s ↔ view loc msg (prefixD pos s) l = view loc msg (prefixD pos s) w := by
  simp only [near, mem_filter, mem_univ, true_and, sepQ_sqB]
  rw [view_eq_iff]
  constructor
  · rintro (rfl | hlt)
    · exact ⟨rfl, fun _ _ => rfl⟩
    · have hloc : loc w = loc l := by
        by_contra h
        rw [sepPos_zero loc msg pos T h] at hlt
        omega
      refine ⟨hloc.symm, fun j hj => ?_⟩
      simp only [prefixD, mem_filter, mem_univ, true_and] at hj
      by_contra hne
      have := sepPos_le_of_diff loc msg pos T hloc (Ne.symm hne)
      omega
  · rintro ⟨hloc, hmsg⟩
    right
    unfold sepPos
    rw [if_neg (not_not.mpr hloc.symm)]
    split_ifs with hs
    · rw [Finset.lt_inf'_iff]
      intro j hj
      simp only [mem_filter, mem_univ, true_and] at hj
      by_contra hle
      push_neg at hle
      exact hj (hmsg j (by simp [prefixD]; omega)).symm
    · exact hsT

/-- **Anytime stopping.**  Below `T`, the receiver at `w` can stop at capacity `s` iff its view class at `s` has an
action acceptable throughout. -/
theorem anytime_stop_iff (safe : World → Finset Act) (s : ℕ) (hsT : s < T) (w : World) :
    CommonSafe safe (near (sqB loc msg pos T) w s)
      ↔ ∃ a, ∀ l, view loc msg (prefixD pos s) l = view loc msg (prefixD pos s) w → a ∈ safe l := by
  unfold CommonSafe
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun l hl => ha l ((near_iff_view loc msg pos T s hsT w l).2 hl)⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, fun l hl => ha l ((near_iff_view loc msg pos T s hsT w l).1 hl)⟩

/-- **The worst-case anytime depth is the fixed decision depth** (paper B's `max_order_iff`, whose ultrametric
hypothesis the broadcast satisfies). -/
theorem worst_anytime_depth_iff [Nonempty Act] (safe : World → Finset Act) (hsafe : ∀ w, (safe w).Nonempty)
    (hT : ∀ j, pos j < T) (s : ℕ) (hs : 1 ≤ s) :
    (∃ w, s ≤ dOrder (sqB loc msg pos T) safe hsafe w)
      ↔ ∃ H, Unsafe safe H ∧ H.Nonempty ∧ ∀ u ∈ H, ∀ v ∈ H, u ≠ v → s ≤ sepPos loc msg pos T u v := by
  have hsym : ∀ u v, sepQ (sqB loc msg pos T) u v = sepQ (sqB loc msg pos T) v u := by
    intro u v; rw [sepQ_sqB, sepQ_sqB]; exact sepPos_symm loc msg pos T u v
  have hU : ∀ u v x, min (sepQ (sqB loc msg pos T) u x) (sepQ (sqB loc msg pos T) x v)
      ≤ sepQ (sqB loc msg pos T) u v := by
    intro u v x; rw [sepQ_sqB, sepQ_sqB, sepQ_sqB]; exact sepPos_ultrametric loc msg pos T hT u v x
  have h := max_order_iff (sqB loc msg pos T) safe hsafe hsym hU s hs
  simp only [sepQ_sqB] at h
  exact h

end CIGAMF.P13.MarlAdaptiveDepth

#print axioms CIGAMF.P13.MarlAdaptiveDepth.sepPos_symm
#print axioms CIGAMF.P13.MarlAdaptiveDepth.sepPos_ultrametric
#print axioms CIGAMF.P13.MarlAdaptiveDepth.near_iff_view
#print axioms CIGAMF.P13.MarlAdaptiveDepth.anytime_stop_iff
#print axioms CIGAMF.P13.MarlAdaptiveDepth.worst_anytime_depth_iff
