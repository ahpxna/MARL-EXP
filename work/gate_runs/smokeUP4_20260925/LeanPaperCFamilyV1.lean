import «LeanPaperCInstantiationV1»

/-!
# Paper C: the family itself, and the two heavy items

Everything in the C development is stated for the *predicates* `IsEvenFamily` and
`IsOddFamily` — weights in `{-3,-1,1,3}` with total `0` or `-1`.  Those predicates do NOT
pin the family, and in particular they do not force it to have exactly two heavy items:
`(1,1,-1,-1)` satisfies `IsEvenFamily` with **no** heavy item at all, which
`isEvenFamily_not_forcing_two_heavy` exhibits.  So `|heavySet| = 2`, which the endpoint
argument uses, is a property of the concrete

    g_m = (-3, -1 x p, +1 x q, +3),    p = ceil((m-2)/2),  q = floor((m-2)/2),

and it has to be proved there rather than inherited from a predicate.  This module writes
`g_m` down, proves it satisfies the right predicate at each parity, and computes its heavy
set.

On `ℕ` division, `ceil((m-2)/2) = (m-1)/2`, which is what `gFamily` uses; the total is then
`(m-2) - 2*((m-1)/2)`, equal to `0` for even `m` and `-1` for odd `m` — the two predicates,
from one computation.
-/

namespace CIGAMF.P13.PaperCFamily

open Finset
open CIGAMF.P13.PaperCRanking
open CIGAMF.P13.PaperCInstantiation

/-- **The family**, on `ℕ` indices. -/
noncomputable def gN (m j : ℕ) : ℝ :=
  if j = 0 then -3 else if j = m - 1 then 3 else if j ≤ (m - 1) / 2 then -1 else 1

/-- **The family.**  Heavy `-3` first, heavy `+3` last, `p` light negatives then `q` light
positives in between. -/
noncomputable def gFamily (m : ℕ) : Ranking m := fun i => gN m (i : ℕ)

theorem gFamily_apply (m : ℕ) (i : Fin m) : gFamily m i = gN m (i : ℕ) := rfl

theorem gN_weights (m j : ℕ) :
    gN m j = -3 ∨ gN m j = -1 ∨ gN m j = 1 ∨ gN m j = 3 := by
  unfold gN
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))

theorem gFamily_weights (m : ℕ) (i : Fin m) :
    gFamily m i = -3 ∨ gFamily m i = -1 ∨ gFamily m i = 1 ∨ gFamily m i = 3 :=
  gN_weights m (i : ℕ)

theorem heavy_eq_one_iff (w : ℝ) : heavy w = 1 ↔ |w| = 3 := by
  unfold heavy
  by_cases h : |w| = 3
  · simp [h]
  · simp [h]

/-- A range split at the sign change: `p` negatives then `q` positives. -/
theorem split_sum (p q : ℕ) :
    ∑ j ∈ Finset.range (p + q), (if j + 1 ≤ p then (-1 : ℝ) else 1) = -(p : ℝ) + (q : ℝ) := by
  rw [Finset.sum_range_add]
  have hlow : ∀ j ∈ Finset.range p, (if j + 1 ≤ p then (-1 : ℝ) else 1) = -1 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [if_pos (by omega)]
  have hhigh : ∀ j ∈ Finset.range q, (if p + j + 1 ≤ p then (-1 : ℝ) else 1) = 1 := by
    intro j _
    rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh,
    Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
    nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- **The total, in one computation.**  Peel the two heavy endpoints; the middle splits at
the sign change into `p` negatives and `n - p` positives. -/
theorem gFamily_total (n : ℕ) (hn : 1 ≤ n) :
    ∑ i, gFamily (n + 2) i = (n : ℝ) - 2 * (((n + 1) / 2 : ℕ) : ℝ) := by
  classical
  have hp : (n + 1) / 2 ≤ n := by omega
  have hsum : ∑ i : Fin (n + 2), gFamily (n + 2) i
      = ∑ j ∈ Finset.range (n + 2), gN (n + 2) j := by
    simpa [gFamily_apply] using
      (Fin.sum_univ_eq_sum_range (fun j => gN (n + 2) j) (n + 2))
  rw [hsum, Finset.sum_range_succ, Finset.sum_range_succ']
  have hlast : gN (n + 2) (n + 1) = 3 := by
    unfold gN; rw [if_neg (by omega), if_pos (by omega)]
  have hfirst : gN (n + 2) 0 = -3 := by unfold gN; rw [if_pos rfl]
  have hmid : ∀ j ∈ Finset.range n,
      gN (n + 2) (j + 1) = if j + 1 ≤ (n + 1) / 2 then (-1 : ℝ) else 1 := by
    intro j hj
    rw [Finset.mem_range] at hj
    unfold gN
    rw [if_neg (by omega), if_neg (by omega), show n + 2 - 1 = n + 1 from by omega]
  rw [Finset.sum_congr rfl hmid, hfirst, hlast]
  have hsplit := split_sum ((n + 1) / 2) (n - (n + 1) / 2)
  rw [show (n + 1) / 2 + (n - (n + 1) / 2) = n from by omega] at hsplit
  rw [hsplit]
  have hcast : ((n - (n + 1) / 2 : ℕ) : ℝ) = (n : ℝ) - (((n + 1) / 2 : ℕ) : ℝ) := by
    have : ((n + 1) / 2 : ℕ) ≤ n := hp
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast]
  ring

/-- **`g_m` is an even family at even `m`.** -/
theorem gFamily_isEvenFamily (n : ℕ) (hn : 1 ≤ n) (hpar : n % 2 = 0) :
    IsEvenFamily (gFamily (n + 2)) := by
  refine ⟨fun i => gFamily_weights (n + 2) i, ?_⟩
  rw [gFamily_total n hn]
  have : ((n + 1) / 2 : ℕ) = n / 2 := by omega
  rw [this]
  have h2 : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) := by
    have hnn : n = 2 * (n / 2) := by omega
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hnn
  rw [h2]; ring

/-- **`g_m` is an odd family at odd `m`.** -/
theorem gFamily_isOddFamily (n : ℕ) (hn : 1 ≤ n) (hpar : n % 2 = 1) :
    IsOddFamily (gFamily (n + 2)) := by
  refine ⟨fun i => gFamily_weights (n + 2) i, ?_⟩
  rw [gFamily_total n hn]
  have h2 : (n : ℝ) = 2 * (((n + 1) / 2 : ℕ) : ℝ) - 1 := by
    have hnn : n + 1 = 2 * ((n + 1) / 2) := by omega
    have : ((n + 1 : ℕ) : ℝ) = 2 * (((n + 1) / 2 : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hnn
    push_cast at this
    linarith
  rw [h2]; ring

/-- **Membership in the heavy set, as a condition on the index.** -/
theorem mem_heavySet_gFamily (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 2)) :
    i ∈ heavySet (gFamily (n + 2)) ↔ ((i : ℕ) = 0 ∨ (i : ℕ) = n + 1) := by
  classical
  rw [mem_heavySet, heavy_eq_one_iff, gFamily_apply]
  unfold gN
  constructor
  · intro hi
    by_contra hc
    push_neg at hc
    rw [if_neg hc.1, if_neg (by omega)] at hi
    split_ifs at hi <;> norm_num at hi
  · intro hi
    rcases hi with hi | hi
    · rw [if_pos hi]; norm_num
    · rw [if_neg (by omega), if_pos (by omega)]; norm_num

/-- **The heavy set is the two endpoints.** -/
theorem gFamily_heavySet (n : ℕ) (hn : 1 ≤ n) :
    heavySet (gFamily (n + 2)) = {⟨0, by omega⟩, ⟨n + 1, by omega⟩} := by
  classical
  ext i
  rw [mem_heavySet_gFamily n hn]
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

theorem gFamily_heavy_card (n : ℕ) (hn : 1 ≤ n) :
    (heavySet (gFamily (n + 2))).card = 2 := by
  classical
  rw [gFamily_heavySet n hn, Finset.card_insert_of_notMem, Finset.card_singleton]
  simp only [Finset.mem_singleton, Fin.ext_iff]
  omega

/-- **The predicate does not force two heavy items.**  `(1,1,-1,-1)` satisfies
`IsEvenFamily` and has an empty heavy set, so `|heavySet| = 2` is a fact about `g_m` and not
a consequence of the hypotheses the rest of the development carries. -/
theorem isEvenFamily_not_forcing_two_heavy :
    ∃ π : Ranking 4, IsEvenFamily π ∧ (heavySet π).card ≠ 2 := by
  classical
  refine ⟨fun i => if (i : ℕ) < 2 then 1 else -1, ⟨fun i => ?_, ?_⟩, ?_⟩
  · by_cases h : (i : ℕ) < 2
    · simp [h]
    · simp [h]
  · rw [Fin.sum_univ_four]
    norm_num
  · have hempty : heavySet (fun i : Fin 4 => if (i : ℕ) < 2 then (1 : ℝ) else -1) = ∅ := by
      ext i
      simp only [mem_heavySet, Finset.notMem_empty, iff_false, heavy_eq_one_iff]
      by_cases h : (i : ℕ) < 2 <;> simp [h]
    rw [hempty]
    simp

/-! ## Audit -/

#print axioms gFamily_weights
#print axioms gFamily_total
#print axioms gFamily_isEvenFamily
#print axioms gFamily_isOddFamily
#print axioms mem_heavySet_gFamily
#print axioms gFamily_heavySet
#print axioms gFamily_heavy_card
#print axioms isEvenFamily_not_forcing_two_heavy

end CIGAMF.P13.PaperCFamily
