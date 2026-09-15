import Mathlib
import «LeanStructuralStaircaseUnboundedV1»
import «LeanStructuralPrefixCoverDimensionV1»

/-!
# An actual supportOsc family with unbounded prefix-cover dimension

For every positive `r`, the staircase construction has `r` distinct budget
layers with forced unique zero-radius optima.  Those optima are pairwise
incomparable, so fewer than `r` full rankings cannot hit every layer.
-/

namespace CIGAMF.P13.StructuralUnboundedPrefixCoverFamily

open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.StructuralGeometryWitnesses
open CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralStaircaseFamily
open CIGAMF.P13.StructuralStaircaseUnbounded

private theorem osc_zero_eq_anchor
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (g : Ω → ℝ) (anchor : Ω) (h : osc g = 0) :
    ∀ a, g a = g anchor := by
  have hEq : maxVal g = minVal g := by
    simpa [osc] using sub_eq_zero.mp h
  intro a
  linarith [minVal_le g a, le_maxVal g a,
    minVal_le g anchor, le_maxVal g anchor]

theorem omitted_sum_zero_of_radius_zero {r : ℕ}
    (S : Finset (StairRel r))
    (hzero : selectedRadius staircaseF S = 0) :
    ∀ a : StairAction r, sumComponent Sᶜ staircaseF a = 0 := by
  have hosc : osc (sumComponent Sᶜ staircaseF) = 0 := by
    unfold selectedRadius supportOsc at hzero
    linarith
  have hconst := osc_zero_eq_anchor (sumComponent Sᶜ staircaseF) none hosc
  intro a
  calc
    sumComponent Sᶜ staircaseF a =
        sumComponent Sᶜ staircaseF none := hconst a
    _ = 0 := by simp [sumComponent, staircaseF]

theorem staircaseSelected_unique_optimal {r : ℕ} (hr : 0 < r)
    (t : Fin r) (S : Finset (StairRel r))
    (hOptimal : EpsilonOptimalAt (selectedRadius staircaseF) 0
      (staircaseSelected t).card S) :
    S = staircaseSelected t := by
  have hle := hOptimal.2 (staircaseSelected t) rfl
  rw [staircaseSelected_radius_zero] at hle
  have hnonneg := selectedRadius_nonneg staircaseF S
  have hzero : selectedRadius staircaseF S = 0 := by linarith
  have hsum := omitted_sum_zero_of_radius_zero S hzero
  have hcardCompl : Sᶜ.card = (staircaseSelected t)ᶜ.card := by
    rw [Finset.card_compl, Finset.card_compl, hOptimal.1]
  rcases sum_zero_set_eq_empty_or_staircaseBlock hr Sᶜ hsum with hempty | ⟨s, hs⟩
  · have hright : (staircaseSelected t)ᶜ.card = t.val + 2 := by
      simp [staircaseSelected, staircaseBlock_card]
    rw [hempty] at hcardCompl
    simp [hright] at hcardCompl
  · have hst : s = t := by
      have hc : s.val + 2 = t.val + 2 := by
        calc
          s.val + 2 = (staircaseBlock s).card := (staircaseBlock_card s).symm
          _ = Sᶜ.card := by rw [hs]
          _ = (staircaseSelected t)ᶜ.card := hcardCompl
          _ = (staircaseBlock t).card := by simp [staircaseSelected]
          _ = t.val + 2 := staircaseBlock_card t
      apply Fin.ext
      omega
    subst s
    apply compl_injective
    simpa [staircaseSelected] using hs

private theorem prefixSet_mono_staircase {r : ℕ}
    (ranking : List (StairRel r)) {k l : ℕ} (hkl : k ≤ l) :
    prefixSet ranking k ⊆ prefixSet ranking l := by
  intro x hx
  have hp : ranking.take k <+: ranking.take l :=
    List.take_prefix_take_left hkl
  have hxList : x ∈ ranking.take k := by simpa [prefixSet] using hx
  have : x ∈ ranking.take l := hp.subset hxList
  simpa [prefixSet] using this

/-- The explicit family is unbounded: at parameter `r`, its zero-tolerance
prefix-cover dimension is at least `r`. -/
theorem STRUCT_UNBOUNDED_staircase_prefix_dimension_ge {r : ℕ} (hr : 0 < r) :
    ¬ PrefixCoverDimensionAtMost (selectedRadius (staircaseF (r := r))) 0
      (r - 1) := by
  classical
  intro hDim
  rcases hDim with ⟨menu, hMenuCard, hCover⟩
  have hLayer : ∀ t : Fin r,
      ∃ ranking ∈ menu,
        EpsilonOptimalAt (selectedRadius (staircaseF (r := r))) 0
          (staircaseSelected t).card
          (prefixSet ranking (staircaseSelected t).card) := by
    intro t
    exact hCover.2.2 (staircaseSelected t).card
      (Finset.card_le_univ (staircaseSelected t))
  let rankFor : Fin r → List (StairRel r) := fun t => Classical.choose (hLayer t)
  have rankFor_mem (t : Fin r) : rankFor t ∈ menu :=
    (Classical.choose_spec (hLayer t)).1
  have rankFor_opt (t : Fin r) :
      EpsilonOptimalAt (selectedRadius (staircaseF (r := r))) 0
        (staircaseSelected t).card
        (prefixSet (rankFor t) (staircaseSelected t).card) :=
    (Classical.choose_spec (hLayer t)).2
  have rankFor_prefix (t : Fin r) :
      prefixSet (rankFor t) (staircaseSelected t).card =
        staircaseSelected t :=
    staircaseSelected_unique_optimal hr t _ (rankFor_opt t)
  have rankFor_injective : Function.Injective rankFor := by
    intro s t heq
    by_contra hst
    by_cases hcard : (staircaseSelected s).card ≤ (staircaseSelected t).card
    · have hsub : staircaseSelected s ⊆ staircaseSelected t := by
        rw [← rankFor_prefix s, ← rankFor_prefix t, heq]
        exact prefixSet_mono_staircase (rankFor t) hcard
      exact staircaseSelected_incomparable hst hsub
    · have hcard' : (staircaseSelected t).card ≤ (staircaseSelected s).card := by omega
      have hsub : staircaseSelected t ⊆ staircaseSelected s := by
        rw [← rankFor_prefix t, ← rankFor_prefix s, ← heq]
        exact prefixSet_mono_staircase (rankFor s) hcard'
      exact staircaseSelected_incomparable (Ne.symm hst) hsub
  let used : Finset (List (StairRel r)) := Finset.univ.image rankFor
  have hUsedCard : used.card = r := by
    unfold used
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro a ha b hb hab
      exact rankFor_injective hab
  have hUsedSubset : used ⊆ menu := by
    intro ranking hranking
    rcases Finset.mem_image.mp hranking with ⟨t, -, rfl⟩
    exact rankFor_mem t
  have hLower := Finset.card_le_card hUsedSubset
  rw [hUsedCard] at hLower
  omega

end CIGAMF.P13.StructuralUnboundedPrefixCoverFamily
