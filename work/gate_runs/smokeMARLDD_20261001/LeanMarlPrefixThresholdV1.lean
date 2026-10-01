import Mathlib

/-!
# Prefix decoding in threshold form

In the prefix channel a receiver `i` with capacity `K` decodes "the first `K` senders of the committed order other than
itself".  With the order given by a ranking `pos` (injective, values below `m`), this module proves that set equals
`{j ≠ i | pos j < r}` for the threshold `r = K + [pos i < K]`: the form used by `LeanMarlRelayOneHopV1.prefixDecoded`,
where it yields the covering receiver (`prefix_cover_exists`) and the decoded head (`prefix_head_decoded`).

## WHAT IS PROVED
* `card_filter_lt` — a ranking has exactly `p` senders at positions below `p ≤ m` (the argument of
  `LeanStructuralRetainedMarginalV1.card_prefixSet`, restated on `Fin m`).
* `rankOthers_eq` — the number of senders other than `i` ahead of `j ≠ i` is `pos j - [pos i < pos j]`.
* `firstK_eq_threshold` — "first `K` others" equals the threshold form, for every ranking, receiver and capacity.
* `nested` — decoded sets are nested: a receiver with the larger threshold decodes every sender the other decodes,
  except possibly the other receiver's own... no: except the larger receiver itself.

## WHAT THIS DOES NOT ESTABLISH
- Anything about the cap rule (the stream limited to `c` packets); that intersects the decoded set with a fixed prefix
  and keeps the threshold form with `min(r, c)` excluding the receiver's own slot, which is not proved here.
-/

namespace CIGAMF.P13.MarlPrefixThreshold

open Finset

variable {m : ℕ}

/-- A ranking: distinct positions below `m` (as `LeanStructuralRetainedMarginalV1.IsRanking` on `Fin m`). -/
def IsRanking (pos : Fin m → ℕ) : Prop := Function.Injective pos ∧ ∀ i, pos i < m

/-- Senders other than `i` ranked ahead of `j`. -/
def rankOthers (pos : Fin m → ℕ) (i j : Fin m) : ℕ := (univ.filter fun k => k ≠ i ∧ pos k < pos j).card

/-- "The first `K` senders other than `i`". -/
def firstKOthers (pos : Fin m → ℕ) (K : ℕ) (i : Fin m) : Finset (Fin m) :=
  univ.filter fun j => j ≠ i ∧ rankOthers pos i j < K

/-- The decoding threshold of receiver `i`. -/
def threshold (pos : Fin m → ℕ) (K : ℕ) (i : Fin m) : ℕ := if pos i < K then K + 1 else K

/-- The threshold form (as in `LeanMarlRelayOneHopV1.prefixDecoded`). -/
def prefixDecoded (pos r : Fin m → ℕ) (i : Fin m) : Finset (Fin m) :=
  univ.filter fun j => j ≠ i ∧ pos j < r i

theorem card_filter_lt {pos : Fin m → ℕ} (h : IsRanking pos) (p : ℕ) (hp : p ≤ m) :
    (univ.filter fun k => pos k < p).card = p := by
  have himg : image pos univ = range m := by
    refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      exact mem_range.mpr (h.2 i)
    · rw [card_range, card_image_of_injective _ h.1, card_univ, Fintype.card_fin]
  have hpre : image pos (univ.filter fun k => pos k < p) = range p := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      simp only [mem_filter, mem_univ, true_and] at hi
      exact mem_range.mpr hi
    · intro hx
      have hxm : x ∈ image pos univ := by rw [himg]; exact mem_range.mpr (by simp at hx; omega)
      obtain ⟨i, _, rfl⟩ := mem_image.mp hxm
      exact mem_image.mpr ⟨i, by simpa using mem_range.mp hx, rfl⟩
  calc (univ.filter fun k => pos k < p).card = (image pos (univ.filter fun k => pos k < p)).card :=
        (card_image_of_injective _ h.1).symm
    _ = p := by rw [hpre, card_range]

theorem rankOthers_eq {pos : Fin m → ℕ} (h : IsRanking pos) (i j : Fin m) :
    rankOthers pos i j = pos j - (if pos i < pos j then 1 else 0) := by
  have hset : (univ.filter fun k => k ≠ i ∧ pos k < pos j) = (univ.filter fun k => pos k < pos j).erase i := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_erase]
  unfold rankOthers
  rw [hset]
  have hc := card_filter_lt h (pos j) (le_of_lt (h.2 j))
  split_ifs with hij
  · rw [card_erase_of_mem (by simpa using hij), hc]
  · rw [erase_eq_of_notMem (by simpa using hij), hc]
    simp

theorem firstK_eq_threshold {pos : Fin m → ℕ} (h : IsRanking pos) (K : ℕ) (i : Fin m) :
    firstKOthers pos K i = prefixDecoded pos (threshold pos K) i := by
  ext j
  unfold firstKOthers prefixDecoded threshold
  rw [mem_filter, mem_filter]
  simp only [mem_univ, true_and]
  refine and_congr_right fun hji => ?_
  rw [rankOthers_eq h i j]
  have hne : pos j ≠ pos i := fun he => hji (h.1 he)
  split_ifs <;> omega

/-- **Nestedness.**  A receiver whose threshold is at least another's decodes every sender the other decodes, except
itself. -/
theorem nested (pos r : Fin m → ℕ) (i c : Fin m) (hrc : r i ≤ r c) :
    ∀ j, j ∈ prefixDecoded pos r i → j ≠ c → j ∈ prefixDecoded pos r c := by
  intro j hj hjc
  simp only [prefixDecoded, mem_filter, mem_univ, true_and] at hj ⊢
  exact ⟨hjc, lt_of_lt_of_le hj.2 hrc⟩

/-- The identity ranking on `Fin 4` witnesses the hypotheses, and `firstK_eq_threshold` applies. -/
theorem ranking_witness : IsRanking (m := 4) (fun i => i.val) :=
  ⟨fun a b hab => Fin.ext hab, fun i => i.isLt⟩

theorem threshold_witness :
    firstKOthers (m := 4) (fun i => i.val) 2 0 = prefixDecoded (fun i => i.val) (threshold (fun i => i.val) 2) 0 :=
  firstK_eq_threshold ranking_witness 2 0

end CIGAMF.P13.MarlPrefixThreshold

#print axioms CIGAMF.P13.MarlPrefixThreshold.card_filter_lt
#print axioms CIGAMF.P13.MarlPrefixThreshold.rankOthers_eq
#print axioms CIGAMF.P13.MarlPrefixThreshold.firstK_eq_threshold
#print axioms CIGAMF.P13.MarlPrefixThreshold.nested
#print axioms CIGAMF.P13.MarlPrefixThreshold.threshold_witness
