import «LeanStructuralConstrainedV1»

/-! # Structural B-marg: P3's ACTUAL retained-component trajectory.

`LeanStructuralConstrainedV1` proves the transfer lemma and checks the witness against a
constraint of the form "every budget carries the same expected regret"
(`witness_balanced`).  The audit's objection is correct: that is NOT P3's marginal.  P3's
marginal is the retained-component probability trajectory

    x*_{i,k} = (1/|J|) * #{ j : item i lies in the length-k prefix of ordering j },

a matrix indexed by (item, budget), not a scalar per budget.  This file defines that
object for an arbitrary menu of rankings, proves the constraints it actually satisfies,
computes it exactly on the cyclic menu, and feeds the result into the generic transfer
lemma.

## WHAT IS PROVED

* `card_prefixSet` — a length-`k` prefix of a ranking has exactly `min k n` items.  This
  is what makes the column sums a budget rather than an assumption.
* `retained_nonneg`, `retained_le_one`, `retained_mono` — the trajectory is a probability
  trajectory and is monotone in the budget, because prefixes are nested.
* `retained_col_sum` — `∑_i x*_{i,k} = min k n` for EVERY menu of rankings.  The column
  sum is the budget; no menu can do better or worse on this count.
* `cyclic_retained` — on the cyclic menu the trajectory is exactly `x*_{i,k} = (min k m)/m`,
  identical for every item.  So the uniform trajectory is REALISABLE, not merely feasible
  on paper.
* `retained_transfer` — the free lower bound transfers to the problem constrained by the
  actual trajectory, via `free_bound_transfers`.
* `retained_constrained_eq_free` — with a witness meeting the trajectory, the constrained
  value equals the free value.

## WHAT THIS DOES NOT ESTABLISH

- `retained_col_sum` is an identity every menu satisfies; it does not single out a menu.
  A constraint PRESCRIBING a non-uniform trajectory may exclude the witness and change
  the value, exactly as the previous file warned.
- The cyclic menu is used because its trajectory is computable in closed form.  No claim
  is made that it is the optimal menu for the structural family.
- The trajectory is a marginal of the mixture over orderings.  It does not determine the
  mixture, so two different mixtures with the same trajectory are not distinguished here.
-/

namespace CIGAMF.P13.StructuralRetainedMarginal

open Finset
open CIGAMF.P13.StructuralConstrained

variable {α J : Type*} [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]

/-- A ranking assigns each item a distinct position below the population size. -/
def IsRanking (pos : α → ℕ) : Prop :=
  Function.Injective pos ∧ ∀ i, pos i < Fintype.card α

/-- The length-`k` prefix of a ranking. -/
def prefixSet (pos : α → ℕ) (k : ℕ) : Finset α :=
  Finset.univ.filter (fun i => pos i < k)

/-- **A length-`k` prefix holds exactly `min k n` items.** -/
theorem card_prefixSet (pos : α → ℕ) (h : IsRanking pos) (k : ℕ) :
    (prefixSet pos k).card = min k (Fintype.card α) := by
  classical
  have himg : Finset.image pos Finset.univ = Finset.range (Fintype.card α) := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (h.2 i)
    · rw [Finset.card_range, Finset.card_image_of_injective _ h.1, Finset.card_univ]
  have hpre : Finset.image pos (prefixSet pos k)
      = Finset.range (Fintype.card α) ∩ Finset.range k := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hlt : pos i < k := by
        simpa [prefixSet, Finset.mem_filter] using hi
      exact Finset.mem_inter.mpr ⟨Finset.mem_range.mpr (h.2 i), Finset.mem_range.mpr hlt⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      have : x ∈ Finset.image pos Finset.univ := by rw [himg]; exact hx1
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp this
      refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
      simpa [prefixSet, Finset.mem_filter] using Finset.mem_range.mp hx2
  have hcard : (prefixSet pos k).card
      = (Finset.range (Fintype.card α) ∩ Finset.range k).card := by
    rw [← hpre, Finset.card_image_of_injective _ h.1]
  rw [hcard]
  have hset : Finset.range (Fintype.card α) ∩ Finset.range k
      = Finset.range (min k (Fintype.card α)) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_range, lt_min_iff]
    omega
  rw [hset, Finset.card_range]

/-- **P3's retained-component trajectory** of a menu of rankings under the uniform
mixture: the probability that item `i` survives at budget `k`. -/
noncomputable def retained (pos : J → α → ℕ) (i : α) (k : ℕ) : ℝ :=
  (1 / (Fintype.card J : ℝ))
    * ((Finset.univ.filter (fun j => i ∈ prefixSet (pos j) k)).card : ℝ)

theorem retained_nonneg (pos : J → α → ℕ) (i : α) (k : ℕ) : 0 ≤ retained pos i k := by
  unfold retained
  positivity

theorem retained_le_one [Nonempty J] (pos : J → α → ℕ) (i : α) (k : ℕ) :
    retained pos i k ≤ 1 := by
  classical
  unfold retained
  have hJ : (0:ℝ) < (Fintype.card J : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hle : ((Finset.univ.filter (fun j => i ∈ prefixSet (pos j) k)).card : ℝ)
      ≤ (Fintype.card J : ℝ) := by
    exact_mod_cast Finset.card_filter_le _ _
  rw [one_div, inv_mul_le_one₀ hJ]
  exact hle

/-- Prefixes are nested, so the trajectory is monotone in the budget. -/
theorem retained_mono (pos : J → α → ℕ) (i : α) {k l : ℕ} (hkl : k ≤ l) :
    retained pos i k ≤ retained pos i l := by
  classical
  unfold retained
  have hsub : (Finset.univ.filter (fun j => i ∈ prefixSet (pos j) k))
      ⊆ (Finset.univ.filter (fun j => i ∈ prefixSet (pos j) l)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, prefixSet] at hj ⊢
    exact lt_of_lt_of_le hj hkl
  have hc : ((Finset.univ.filter (fun j => i ∈ prefixSet (pos j) k)).card : ℝ)
      ≤ ((Finset.univ.filter (fun j => i ∈ prefixSet (pos j) l)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hnn : (0:ℝ) ≤ 1 / (Fintype.card J : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left hc hnn

/-- **The column sum is the budget.**  For every menu of rankings,
`∑_i x*_{i,k} = min k n`.  No menu can change this count. -/
theorem retained_col_sum [Nonempty J] (pos : J → α → ℕ)
    (hpos : ∀ j, IsRanking (pos j)) (k : ℕ) :
    ∑ i : α, retained pos i k = ((min k (Fintype.card α) : ℕ) : ℝ) := by
  classical
  unfold retained
  rw [← Finset.mul_sum]
  have hnat : ∑ i : α, (Finset.univ.filter (fun j : J => i ∈ prefixSet (pos j) k)).card
      = ∑ j : J, (prefixSet (pos j) k).card := by
    simp only [prefixSet, Finset.card_filter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.sum_comm
  have hswap : ∑ i : α, ((Finset.univ.filter (fun j : J => i ∈ prefixSet (pos j) k)).card : ℝ)
      = ∑ j : J, ((prefixSet (pos j) k).card : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hnat
  rw [hswap]
  have hconst : ∀ j ∈ (Finset.univ : Finset J),
      ((prefixSet (pos j) k).card : ℝ) = ((min k (Fintype.card α) : ℕ) : ℝ) := by
    intro j _
    rw [card_prefixSet (pos j) (hpos j) k]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hJ : (Fintype.card J : ℝ) ≠ 0 := by
    have : (0:ℝ) < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
    exact ne_of_gt this
  field_simp

/-! ## The cyclic menu, computed exactly. -/

variable {m : ℕ} [NeZero m]

/-- The cyclic menu: ordering `j` starts at `j` and proceeds cyclically. -/
def cyclicPos (j i : ZMod m) : ℕ := (i - j).val

/-- `ZMod.val` is itself a ranking of `ZMod m`. -/
theorem zmod_val_isRanking : IsRanking (fun v : ZMod m => v.val) := by
  refine ⟨ZMod.val_injective m, fun v => ?_⟩
  rw [ZMod.card m]
  exact ZMod.val_lt v

/-- **The cyclic menu realises the uniform trajectory.**  Every item survives at budget
`k` with the same probability `(min k m)/m`. -/
theorem cyclic_retained (i : ZMod m) (k : ℕ) :
    retained (α := ZMod m) (J := ZMod m) cyclicPos i k
      = ((min k (Fintype.card (ZMod m)) : ℕ) : ℝ) / (Fintype.card (ZMod m) : ℝ) := by
  classical
  unfold retained
  have hmem : ∀ j : ZMod m, (i ∈ prefixSet (cyclicPos j) k) ↔ (i - j).val < k := by
    intro j
    unfold prefixSet cyclicPos
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
           fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
  have himg : (Finset.univ.filter (fun j : ZMod m => i ∈ prefixSet (cyclicPos j) k))
      = Finset.image (fun v : ZMod m => i - v)
          (Finset.univ.filter (fun v : ZMod m => v.val < k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hmem]
    constructor
    · intro hj
      refine ⟨i - j, ?_, by ring⟩
      simpa using hj
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
  have hinj : Function.Injective (fun v : ZMod m => i - v) := fun a b hab => by
    simpa [sub_right_inj] using hab
  rw [himg, Finset.card_image_of_injective _ hinj]
  have hcount : (Finset.univ.filter (fun v : ZMod m => v.val < k)).card
      = min k (Fintype.card (ZMod m)) := by
    simpa [prefixSet] using card_prefixSet (α := ZMod m) (fun v => v.val) zmod_val_isRanking k
  rw [hcount, one_div, inv_mul_eq_div]

/-! ## Feeding the actual trajectory into the transfer lemma. -/

variable {Ord : Type*} [Fintype Ord]

/-- **The transfer, with P3's actual marginal.**  A free lower bound holds under the
constraint that the mixture realises a prescribed retained trajectory. -/
theorem retained_transfer (val : (Ord → ℝ) → ℝ) (Feasible : (Ord → ℝ) → Prop)
    (traj : (Ord → ℝ) → α → ℕ → ℝ) (target : α → ℕ → ℝ) (V : ℝ)
    (hfree : ∀ P, Feasible P → V ≤ val P) :
    ∀ P, Feasible P → (∀ i k, traj P i k = target i k) → V ≤ val P :=
  free_bound_transfers val Feasible (fun P => ∀ i k, traj P i k = target i k) V hfree

/-- …and with a witness meeting the trajectory, the constrained value equals the free
value. -/
theorem retained_constrained_eq_free (val : (Ord → ℝ) → ℝ) (Feasible : (Ord → ℝ) → Prop)
    (traj : (Ord → ℝ) → α → ℕ → ℝ) (target : α → ℕ → ℝ) (V : ℝ) (P₀ : Ord → ℝ)
    (hfree : ∀ P, Feasible P → V ≤ val P)
    (hF₀ : Feasible P₀) (hT₀ : ∀ i k, traj P₀ i k = target i k) (hval : val P₀ = V) :
    IsLeast {v | ∃ P, Feasible P ∧ (∀ i k, traj P i k = target i k) ∧ val P = v} V :=
  constrained_eq_free val Feasible (fun P => ∀ i k, traj P i k = target i k) V P₀
    hfree hF₀ hT₀ hval

#print axioms card_prefixSet
#print axioms retained_nonneg
#print axioms retained_le_one
#print axioms retained_mono
#print axioms retained_col_sum
#print axioms cyclic_retained
#print axioms retained_transfer
#print axioms retained_constrained_eq_free

end CIGAMF.P13.StructuralRetainedMarginal
