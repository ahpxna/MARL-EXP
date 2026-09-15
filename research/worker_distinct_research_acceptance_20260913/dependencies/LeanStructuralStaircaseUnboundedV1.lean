import Mathlib
import «LeanStructuralStaircaseFamilyV1»

/-!
# Zero-radius characterization for the staircase supportOsc family

This module proves the non-numerical core needed for an unbounded
prefix-cover lower bound: the only nonempty omitted sets with radius zero are
the designated positive-prefix/negative-staircase blocks.
-/

namespace CIGAMF.P13.StructuralStaircaseUnbounded

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.StructuralStaircaseFamily

def negativeAt {r : ℕ} (T : Finset (StairRel r)) (i : Fin r) :
    Finset (StairRel r) :=
  T.filter (fun j => j.2 = true ∧ i ≤ j.1)

def negativePart {r : ℕ} (T : Finset (StairRel r)) :
    Finset (StairRel r) :=
  T.filter (fun j => j.2 = true)

theorem staircase_sum_formula {r : ℕ} (T : Finset (StairRel r)) (i : Fin r) :
    sumComponent T staircaseF (some i) =
      (if (i, false) ∈ T then 1 else 0) - (negativeAt T i).card := by
  classical
  unfold sumComponent
  have hpoint : ∀ j : StairRel r,
      staircaseF j (some i) =
        (if j = (i, false) then 1 else 0) -
          (if j.2 = true ∧ i ≤ j.1 then 1 else 0) := by
    rintro ⟨j, b⟩
    cases b
    · simp [staircaseF]
    · by_cases h : i ≤ j <;> simp [staircaseF, h]
  simp_rw [hpoint, Finset.sum_sub_distrib]
  simp [negativeAt]

theorem negativeAt_zero_eq_negativePart {r : ℕ} (hr : 0 < r)
    (T : Finset (StairRel r)) :
    negativeAt T ⟨0, hr⟩ = negativePart T := by
  classical
  ext j
  simp only [negativeAt, negativePart, Finset.mem_filter]
  constructor
  · rintro ⟨hjT, hjNeg, -⟩
    exact ⟨hjT, hjNeg⟩
  · rintro ⟨hjT, hjNeg⟩
    refine ⟨hjT, hjNeg, ?_⟩
    change 0 ≤ j.1.val
    omega

theorem negativePart_card_le_one_of_sum_zero {r : ℕ} (hr : 0 < r)
    (T : Finset (StairRel r))
    (hzero : ∀ a : StairAction r, sumComponent T staircaseF a = 0) :
    (negativePart T).card ≤ 1 := by
  let i0 : Fin r := ⟨0, hr⟩
  have h := hzero (some i0)
  rw [staircase_sum_formula, negativeAt_zero_eq_negativePart hr] at h
  by_cases hp : (i0, false) ∈ T
  · simp [hp] at h
    have hcR : ((negativePart T).card : ℝ) = 1 := by linarith
    have hc : (negativePart T).card = 1 := by exact_mod_cast hcR
    omega
  · simp [hp] at h
    simp [h]

private theorem negativeAt_subset_negativePart {r : ℕ}
    (T : Finset (StairRel r)) (i : Fin r) :
    negativeAt T i ⊆ negativePart T := by
  intro j hj
  simp [negativeAt, negativePart] at hj ⊢
  exact ⟨hj.1, hj.2.1⟩

private theorem no_negative_of_negativePart_empty {r : ℕ}
    (T : Finset (StairRel r)) (hneg : negativePart T = ∅)
    (j : StairRel r) (hj : j ∈ T) : j.2 = false := by
  cases hb : j.2 with
  | false => simpa using hb
  | true =>
      have : j ∈ negativePart T := by simp [negativePart, hj, hb]
      simpa [hneg] using this

theorem sum_zero_and_no_negative_implies_empty {r : ℕ}
    (T : Finset (StairRel r))
    (hzero : ∀ a : StairAction r, sumComponent T staircaseF a = 0)
    (hneg : negativePart T = ∅) : T = ∅ := by
  classical
  ext j
  simp only [Finset.notMem_empty, iff_false]
  intro hj
  have hb := no_negative_of_negativePart_empty T hneg j hj
  rcases j with ⟨i, b⟩
  simp only at hb
  subst b
  have h := hzero (some i)
  rw [staircase_sum_formula] at h
  have hAt : negativeAt T i = ∅ := by
    ext x
    simp only [Finset.notMem_empty, iff_false]
    intro hx
    have hx' := negativeAt_subset_negativePart T i hx
    simpa [hneg] using hx'
  simp [hj, hAt] at h

private theorem negativePart_singleton_has_negative_second {r : ℕ}
    (T : Finset (StairRel r)) (j : StairRel r)
    (hneg : negativePart T = {j}) : j.2 = true := by
  have hj : j ∈ negativePart T := by simp [hneg]
  have hj' : j ∈ T ∧ j.2 = true := by
    simpa [negativePart] using hj
  exact hj'.2

private theorem negative_membership_of_singleton {r : ℕ}
    (T : Finset (StairRel r)) (t : Fin r)
    (hneg : negativePart T = {(t, true)}) (j : Fin r) :
    (j, true) ∈ T ↔ j = t := by
  constructor
  · intro hj
    have : (j, true) ∈ negativePart T := by simp [negativePart, hj]
    simpa [hneg] using this
  · intro hj
    subst j
    have : (t, true) ∈ negativePart T := by simp [hneg]
    have ht : (t, true) ∈ T ∧ (true = true) := by
      simpa [negativePart] using this
    exact ht.1

private theorem negativeAt_of_singleton {r : ℕ}
    (T : Finset (StairRel r)) (t i : Fin r)
    (hneg : negativePart T = {(t, true)}) :
    negativeAt T i = if i ≤ t then {(t, true)} else ∅ := by
  classical
  ext j
  rcases j with ⟨j, b⟩
  cases b
  · by_cases hit : i ≤ t <;> simp [negativeAt, hit]
  · by_cases hjt : j = t
    · subst j
      by_cases hit : i ≤ t <;>
        simp [negativeAt, negative_membership_of_singleton T t hneg, hit]
    · by_cases hit : i ≤ t <;>
        simp [negativeAt, negative_membership_of_singleton T t hneg, hit, hjt]

private theorem positive_membership_of_singleton {r : ℕ}
    (T : Finset (StairRel r)) (t i : Fin r)
    (hzero : ∀ a : StairAction r, sumComponent T staircaseF a = 0)
    (hneg : negativePart T = {(t, true)}) :
    (i, false) ∈ T ↔ i ≤ t := by
  have h := hzero (some i)
  rw [staircase_sum_formula, negativeAt_of_singleton T t i hneg] at h
  by_cases hit : i ≤ t <;> by_cases hp : (i, false) ∈ T <;>
    simp [hit, hp] at h ⊢

theorem sum_zero_set_eq_empty_or_staircaseBlock {r : ℕ} (hr : 0 < r)
    (T : Finset (StairRel r))
    (hzero : ∀ a : StairAction r, sumComponent T staircaseF a = 0) :
    T = ∅ ∨ ∃ t : Fin r, T = staircaseBlock t := by
  classical
  have hcard := negativePart_card_le_one_of_sum_zero hr T hzero
  interval_cases hc : (negativePart T).card
  · left
    apply sum_zero_and_no_negative_implies_empty T hzero
    exact Finset.card_eq_zero.mp hc
  · right
    rcases Finset.card_eq_one.mp hc with ⟨j, hj⟩
    have hb := negativePart_singleton_has_negative_second T j hj
    rcases j with ⟨t, b⟩
    simp only at hb
    subst b
    refine ⟨t, ?_⟩
    ext j
    rcases j with ⟨i, b⟩
    cases b
    · simp [staircaseBlock,
        positive_membership_of_singleton T t i hzero hj]
    · simp [staircaseBlock,
        negative_membership_of_singleton T t hj]

end CIGAMF.P13.StructuralStaircaseUnbounded
