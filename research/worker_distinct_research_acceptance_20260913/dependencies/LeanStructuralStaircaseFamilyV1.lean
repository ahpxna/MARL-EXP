import Mathlib
import «LeanStructuralPrefixCoverDimensionV1»
import «LeanStructuralGeometryWitnessesV4»

/-!
# Staircase supportOsc family (parametric branch)

This file starts the actual all-dimension construction suggested by the exact
`chi >= 5` search.  Relations come in positive/negative pairs.  A negative
relation `t` is cancelled, at every support coordinate, by precisely the
positive prefix `0,...,t`.  The resulting zero-radius omitted blocks have
different cardinalities and are pairwise incomparable.
-/

namespace CIGAMF.P13.StructuralStaircaseFamily

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.StructuralRankability
open CIGAMF.V4.StructuralGeometryWitnesses
open CIGAMF.P13.StructuralPrefixCoverDimension

abbrev StairRel (r : ℕ) := Fin r × Bool
abbrev StairAction (r : ℕ) := Option (Fin r)

/-- Positive relation `i` is the `i`-th basis vector.  Negative relation `t`
is minus the indicator of the coordinate prefix through `t`.  `none` is a
zero anchor support point. -/
def staircaseF {r : ℕ} (j : StairRel r) (a : StairAction r) : ℝ :=
  match a with
  | none => 0
  | some i =>
      if j.2 then
        if i ≤ j.1 then -1 else 0
      else
        if j.1 = i then 1 else 0

/-- The omitted block whose negative staircase vector is exactly cancelled by
its positive prefix. -/
def staircaseBlock {r : ℕ} (t : Fin r) : Finset (StairRel r) :=
  insert (t, true) ((Finset.Iic t).image (fun i => (i, false)))

def staircaseSelected {r : ℕ} (t : Fin r) : Finset (StairRel r) :=
  (staircaseBlock t)ᶜ

private theorem negative_not_in_positive_prefix {r : ℕ} (t : Fin r) :
    (t, true) ∉ (Finset.Iic t).image (fun i => (i, false)) := by
  simp

theorem staircaseBlock_card {r : ℕ} (t : Fin r) :
    (staircaseBlock t).card = t.val + 2 := by
  classical
  rw [staircaseBlock, Finset.card_insert_of_notMem (negative_not_in_positive_prefix t),
    Finset.card_image_iff.mpr]
  · simp
  · intro i hi j hj h
    simpa using congrArg Prod.fst h

private theorem positive_prefix_sum {r : ℕ} (t i : Fin r) :
    ((Finset.Iic t).image (fun a => (a, false))).sum
        (fun j => staircaseF j (some i)) = if i ≤ t then 1 else 0 := by
  classical
  by_cases hit : i ≤ t
  · rw [Finset.sum_eq_single (i, false)]
    · simp [staircaseF, hit]
    · intro b hb hne
      rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
      have hai : a ≠ i := by
        intro h
        subst a
        exact hne rfl
      simp [staircaseF, hai]
    · simp [hit]
  · have hzero : ∀ j ∈ (Finset.Iic t).image (fun a => (a, false)),
        staircaseF j (some i) = 0 := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨a, ha, rfl⟩
      have hat : a ≤ t := by simpa using ha
      have hai : a ≠ i := by
        intro h
        subst a
        exact hit hat
      simp [staircaseF, hai]
    rw [Finset.sum_eq_zero hzero]
    simp [hit]

/-- Every designated omitted block has identically zero aggregate response. -/
theorem staircaseBlock_sum_zero {r : ℕ} (t : Fin r)
    (a : StairAction r) :
    sumComponent (staircaseBlock t) staircaseF a = 0 := by
  classical
  cases a with
  | none => simp [sumComponent, staircaseBlock, staircaseF]
  | some i =>
      rw [sumComponent, staircaseBlock,
        Finset.sum_insert (negative_not_in_positive_prefix t),
        positive_prefix_sum]
      by_cases hit : i ≤ t <;> simp [staircaseF, hit]

/-- Hence each designated retained set has exact support-compression radius
zero. -/
theorem staircaseSelected_radius_zero {r : ℕ} (t : Fin r) :
    selectedRadius staircaseF (staircaseSelected t) = 0 := by
  classical
  have hcompl : (staircaseSelected t)ᶜ = staircaseBlock t := by
    simp [staircaseSelected]
  calc
    selectedRadius staircaseF (staircaseSelected t) = (0 - 0 : ℝ) / 2 :=
      selectedRadius_from_extrema staircaseF (staircaseSelected t) 0 0
        (by intro a; rw [hcompl, staircaseBlock_sum_zero])
        (by intro a; rw [hcompl, staircaseBlock_sum_zero])
        none none
        (by rw [hcompl, staircaseBlock_sum_zero])
        (by rw [hcompl, staircaseBlock_sum_zero])
    _ = 0 := by norm_num

theorem staircaseBlocks_incomparable {r : ℕ} {s t : Fin r} (hst : s ≠ t) :
    ¬ staircaseBlock s ⊆ staircaseBlock t := by
  intro hsub
  have hneg : (s, true) ∈ staircaseBlock t :=
    hsub (by simp [staircaseBlock])
  simp [staircaseBlock] at hneg
  exact hst hneg

theorem staircaseSelected_incomparable {r : ℕ} {s t : Fin r} (hst : s ≠ t) :
    ¬ staircaseSelected s ⊆ staircaseSelected t := by
  intro hsub
  have hcomp : staircaseBlock t ⊆ staircaseBlock s := by
    simpa [staircaseSelected] using Finset.compl_subset_compl.mpr hsub
  exact staircaseBlocks_incomparable (Ne.symm hst) hcomp

end CIGAMF.P13.StructuralStaircaseFamily
