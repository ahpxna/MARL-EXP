import «LeanPaperCInstantiationV1»

/-!
# Paper C: the base family `g_m`, and the endpoint identity

The signed-prefix family is built from one base ranking

    g_m = (-3, -1, ..., -1, +1, ..., +1, +3),

with the two heavy weights at the ends and the light weights split evenly between the two
signs.  `gN` is its position-indexed weight and `gFamily` the ranking itself.

Three facts about it are what the rest of Paper C consumes.

* `gFamily_isEvenFamily` -- every weight is one of the four and the total vanishes.  The
  vanishing total is what makes the even sizes special, and it is proved from a reflection:
  `j ↦ m-1-j` flips the sign of every weight, so the sum is its own negative.
* `gFamily_heavy_card` -- exactly two positions are heavy, namely the two ends.
The endpoint identity itself is NOT here: it belongs to `PaperCInstantiation`, which states
it for an arbitrary ranking.
-/

namespace CIGAMF.P13.PaperCFamily

open Finset
open CIGAMF.P13.PaperCRanking
open CIGAMF.P13.PaperCInstantiation

/-! ## The base ranking -/

/-- The base family's weight at position `j`. -/
noncomputable def gN (m j : ℕ) : ℝ :=
  if j = 0 then -3 else if j = m - 1 then 3 else if j ≤ (m - 1) / 2 then -1 else 1

/-- The base ranking `g_m`. -/
noncomputable def gFamily (m : ℕ) : Ranking m := fun i => gN m (i : ℕ)

theorem gFamily_apply (m : ℕ) (i : Fin m) : gFamily m i = gN m (i : ℕ) := rfl

theorem gN_mem (m j : ℕ) :
    gN m j = -3 ∨ gN m j = -1 ∨ gN m j = 1 ∨ gN m j = 3 := by
  unfold gN
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))

theorem gN_zero (m : ℕ) : gN m 0 = -3 := by
  unfold gN; rw [if_pos rfl]

theorem gN_last (m : ℕ) (hm : 2 ≤ m) : gN m (m - 1) = 3 := by
  unfold gN; rw [if_neg (by omega), if_pos rfl]

theorem gN_mid (m j : ℕ) (h0 : j ≠ 0) (hl : j ≠ m - 1) :
    gN m j = if j ≤ (m - 1) / 2 then (-1 : ℝ) else 1 := by
  unfold gN; rw [if_neg h0, if_neg hl]

/-- **The reflection flips every weight.**  This is what makes the total vanish, and it is
why the even sizes behave differently from the odd ones. -/
theorem gN_reflect (m j : ℕ) (hm : 2 ≤ m) (hpar : m % 2 = 0) (hj : j < m) :
    gN m (m - 1 - j) = -(gN m j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have e : m - 1 - 0 = m - 1 := by omega
    rw [e, gN_last m hm, gN_zero m]
    norm_num
  · by_cases hlast : j = m - 1
    · subst hlast
      have e : m - 1 - (m - 1) = 0 := by omega
      rw [e, gN_zero m, gN_last m hm]
    · have h1 : m - 1 - j ≠ 0 := by omega
      have h2 : m - 1 - j ≠ m - 1 := by omega
      have h3 : j ≠ 0 := by omega
      rw [gN_mid m (m - 1 - j) h1 h2, gN_mid m j h3 hlast]
      by_cases hc : j ≤ (m - 1) / 2
      · rw [if_pos hc, if_neg (by omega)]
        norm_num
      · rw [if_neg hc, if_pos (by omega)]

/-- **The total vanishes.** -/
theorem gFamily_total (m : ℕ) (hm : 2 ≤ m) (hpar : m % 2 = 0) :
    ∑ i, gFamily m i = 0 := by
  classical
  have hfin : ∑ i, gFamily m i = ∑ j ∈ Finset.range m, gN m j :=
    Fin.sum_univ_eq_sum_range (fun j => gN m j) m
  have hrefl : ∑ j ∈ Finset.range m, gN m (m - 1 - j)
      = ∑ j ∈ Finset.range m, gN m j :=
    Finset.sum_range_reflect (fun j => gN m j) m
  have hpt : ∀ j ∈ Finset.range m, gN m (m - 1 - j) = -(gN m j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact gN_reflect m j hm hpar hj
  have hneg : ∑ j ∈ Finset.range m, gN m (m - 1 - j)
      = -∑ j ∈ Finset.range m, gN m j := by
    rw [Finset.sum_congr rfl hpt]
    simp
  rw [hfin]
  linarith [hrefl, hneg]

/-- **The base ranking is a member of the even family.** -/
theorem gFamily_isEvenFamily (n : ℕ) (hn : 1 ≤ n) (hpar : n % 2 = 0) :
    IsEvenFamily (gFamily (n + 2)) where
  weight := fun i => gN_mem (n + 2) (i : ℕ)
  total := gFamily_total (n + 2) (by omega) (by omega)

/-! ## The heavy positions are the two ends -/

theorem gN_heavy_iff (m j : ℕ) (hm : 2 ≤ m) (hj : j < m) :
    |gN m j| = 3 ↔ (j = 0 ∨ j = m - 1) := by
  unfold gN
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    rw [if_neg hcon.1, if_neg hcon.2] at h
    split_ifs at h <;> norm_num at h
  · rintro (rfl | h)
    · rw [if_pos rfl]; norm_num
    · rw [if_neg (by omega), if_pos h]; norm_num

theorem gFamily_heavy_card (n : ℕ) (hn : 1 ≤ n) :
    (heavySet (gFamily (n + 2))).card = 2 := by
  classical
  have hm : 2 ≤ n + 2 := by omega
  have hset : heavySet (gFamily (n + 2))
      = {(⟨0, by omega⟩ : Fin (n + 2)), (⟨n + 2 - 1, by omega⟩ : Fin (n + 2))} := by
    ext i
    rw [mem_heavySet]
    unfold heavy
    constructor
    · intro h
      have habs : |gFamily (n + 2) i| = 3 := by
        by_contra hc
        rw [if_neg hc] at h
        norm_num at h
      have := (gN_heavy_iff (n + 2) (i : ℕ) hm i.isLt).mp habs
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases this with h0 | h1
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Fin.ext h1)
    · intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      have habs : |gFamily (n + 2) i| = 3 := by
        refine (gN_heavy_iff (n + 2) (i : ℕ) hm i.isLt).mpr ?_
        rcases h with h | h
        · left; rw [h]
        · right; rw [h]
      rw [if_pos habs]
  rw [hset]
  rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]), Finset.card_singleton]

/-! ## Audit -/

#print axioms gN_mem
#print axioms gN_zero
#print axioms gN_last
#print axioms gN_mid
#print axioms gN_reflect
#print axioms gFamily_total
#print axioms gFamily_isEvenFamily
#print axioms gN_heavy_iff
#print axioms gFamily_heavy_card

end CIGAMF.P13.PaperCFamily
