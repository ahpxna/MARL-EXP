import Mathlib
import «LeanStructuralStaircaseUnboundedV1»
import «LeanStructuralUnboundedPrefixCoverFamilyV1»
import «LeanStructuralOrdinaryChainCharacterizationV1»
import «LeanStructuralGeometryWitnessesV4»

/-!
# Exact prefix-menu law for the staircase supportOsc family

This is the constructive upper branch complementary to the compiled
incomparable-zero-optima lower bound. It uses no DP result: the low-budget
chain is certified by one anchor contrast, while the middle-budget optima are
the already-characterized zero-radius staircase sets.
-/

namespace CIGAMF.P13.StructuralStaircaseExactPrefixCover

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralStaircaseFamily
open CIGAMF.P13.StructuralStaircaseUnbounded
open CIGAMF.P13.StructuralUnboundedPrefixCoverFamily
open CIGAMF.P13.StructuralOrdinaryChainCharacterization
open CIGAMF.P13.StructuralMinimumTransversalWidth
open CIGAMF.V4.StructuralGeometryWitnesses

/-! ## Elementary negative-coordinate counting -/

def negativeUniverse {r : ℕ} : Finset (StairRel r) :=
  Finset.univ.filter fun j => j.2 = true

theorem negativeUniverse_eq_image {r : ℕ} :
    negativeUniverse (r := r) = Finset.univ.image (fun i : Fin r => (i, true)) := by
  classical
  ext j
  rcases j with ⟨i, b⟩
  cases b <;> simp [negativeUniverse]

theorem negativeUniverse_card {r : ℕ} :
    (negativeUniverse (r := r)).card = r := by
  classical
  rw [negativeUniverse_eq_image, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    simpa using congrArg Prod.fst hij

theorem negativePart_subset {r : ℕ} (S : Finset (StairRel r)) :
    negativePart S ⊆ S := by
  intro j hj
  have h : j ∈ S ∧ j.2 = true := by
    simpa [negativePart] using hj
  exact h.1

theorem negativeUniverse_partition {r : ℕ} (S : Finset (StairRel r)) :
    negativeUniverse (r := r) = negativePart S ∪ negativePart Sᶜ := by
  classical
  ext j
  by_cases hS : j ∈ S <;> simp [negativeUniverse, negativePart, hS]

theorem negativeParts_disjoint {r : ℕ} (S : Finset (StairRel r)) :
    Disjoint (negativePart S) (negativePart Sᶜ) := by
  classical
  apply Finset.disjoint_left.mpr
  intro j hjS hjCompl
  have hS : j ∈ S := (negativePart_subset S) hjS
  have hCompl : j ∈ Sᶜ := (negativePart_subset Sᶜ) hjCompl
  have hNotS : j ∉ S := by simpa using hCompl
  exact hNotS hS

/-- If a retained set has cardinality at most `k`, at least `r-k` negative
relations remain omitted. -/
theorem omitted_negative_card_lower {r k : ℕ}
    (S : Finset (StairRel r)) (hCard : S.card ≤ k) :
    r - k ≤ (negativePart Sᶜ).card := by
  classical
  have hPartition := negativeUniverse_partition S
  have hDisjoint := negativeParts_disjoint S
  have hNegS : (negativePart S).card ≤ S.card :=
    Finset.card_le_card (negativePart_subset S)
  have hSum : r = (negativePart S).card + (negativePart Sᶜ).card := by
    calc
      r = (negativeUniverse (r := r)).card := (negativeUniverse_card (r := r)).symm
      _ = (negativePart S ∪ negativePart Sᶜ).card := by rw [← hPartition]
      _ = (negativePart S).card + (negativePart Sᶜ).card :=
        Finset.card_union_of_disjoint hDisjoint
  omega

/-! ## Low-budget optimality from the `some 0` contrast -/

/-- Every retained `k`-set in the low regime leaves enough negative staircase
relations omitted to force the displayed radius lower bound. -/
theorem low_budget_radius_lower {r k : ℕ} (hr : 0 < r)
    (hk : k ≤ r - 1) (S : Finset (StairRel r)) (hCard : S.card = k) :
    ((r - k - 1 : ℕ) : ℝ) / 2 ≤ selectedRadius staircaseF S := by
  classical
  let i0 : Fin r := ⟨0, hr⟩
  let g : StairAction r → ℝ := sumComponent Sᶜ staircaseF
  have hOmitted : r - k ≤ (negativePart Sᶜ).card := by
    apply omitted_negative_card_lower S
    omega
  have hOmittedR : ((r - k : ℕ) : ℝ) ≤ (negativePart Sᶜ).card := by
    exact_mod_cast hOmitted
  have hStep : r - k = (r - k - 1) + 1 := by omega
  have hStepR : ((r - k - 1 : ℕ) : ℝ) + 1 = ((r - k : ℕ) : ℝ) := by
    exact_mod_cast hStep.symm
  have hRecombine : r - k + k = r := by omega
  have hRecombineR : ((r - k : ℕ) : ℝ) + (k : ℝ) = r := by
    exact_mod_cast hRecombine
  have hAtZero : g (some i0) ≤ -((r - k - 1 : ℕ) : ℝ) := by
    have hFormula : g (some i0) =
        (if (i0, false) ∈ Sᶜ then 1 else 0) - (negativePart Sᶜ).card := by
      rw [show g (some i0) = sumComponent Sᶜ staircaseF (some i0) by rfl,
        staircase_sum_formula, negativeAt_zero_eq_negativePart hr]
    rw [hFormula]
    by_cases hp : (i0, false) ∈ Sᶜ
    · rw [if_pos hp]
      norm_num
      linarith
    · rw [if_neg hp]
      norm_num
      linarith
  have hAnchor : g none = 0 := by
    simp [g, sumComponent, staircaseF]
  have hMax : 0 ≤ maxVal g := by
    rw [← hAnchor]
    exact le_maxVal g none
  have hMin : minVal g ≤ g (some i0) := minVal_le g (some i0)
  unfold selectedRadius supportOsc osc
  change ((r - k - 1 : ℕ) : ℝ) / 2 ≤ (maxVal g - minVal g) / 2
  linarith

/-! ## The main low-budget chain -/

/-- The first `k` indices of `Fin r`, with `k < r` carried by the type. -/
def lowIndices {r : ℕ} (k : Fin r) : Finset (Fin r) :=
  ((Finset.range k.val).attach).image
    (fun j : {x // x ∈ Finset.range k.val} =>
      (⟨j.val, lt_trans (Finset.mem_range.mp j.property) k.isLt⟩ : Fin r))

/-- `L_k`: retain precisely the negative relations indexed strictly below `k`.
For `k = 0` this is empty. -/
def lowSelected {r : ℕ} (k : Fin r) : Finset (StairRel r) :=
  (lowIndices k).image (fun i => (i, true))

theorem lowIndices_card {r : ℕ} (k : Fin r) :
    (lowIndices k).card = k.val := by
  classical
  unfold lowIndices
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ hab
    apply Subtype.ext
    exact congrArg Fin.val hab

theorem lowSelected_card {r : ℕ} (k : Fin r) :
    (lowSelected k).card = k.val := by
  classical
  unfold lowSelected
  rw [Finset.card_image_iff.mpr]
  · exact lowIndices_card k
  · intro i _ j _ hij
    exact congrArg Prod.fst hij

theorem mem_lowIndices_iff {r : ℕ} (k : Fin r) (i : Fin r) :
    i ∈ lowIndices k ↔ i.val < k.val := by
  classical
  constructor
  · intro hi
    unfold lowIndices at hi
    rcases Finset.mem_image.mp hi with ⟨a, ha, hai⟩
    have hlt : a.val < k.val := Finset.mem_range.mp a.property
    have hval : i.val = a.val := by
      exact (congrArg Fin.val hai).symm
    omega
  · intro hi
    unfold lowIndices
    apply Finset.mem_image.mpr
    let a : {x // x ∈ Finset.range k.val} := ⟨i.val, Finset.mem_range.mpr hi⟩
    refine ⟨a, by simp [a], ?_⟩
    apply Fin.ext
    rfl

theorem mem_lowSelected_iff {r : ℕ} (k : Fin r) (j : StairRel r) :
    j ∈ lowSelected k ↔ j.2 = true ∧ j.1.val < k.val := by
  classical
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, hij⟩
    have hi' := (mem_lowIndices_iff k i).1 hi
    rcases j with ⟨j, b⟩
    have hfirst : j = i := (congrArg Prod.fst hij).symm
    have hsecond : b = true := (congrArg Prod.snd hij).symm
    subst b
    subst j
    exact ⟨rfl, hi'⟩
  · rintro ⟨hSecond, hlt⟩
    have hi : j.1 ∈ lowIndices k := (mem_lowIndices_iff k j.1).2 hlt
    apply Finset.mem_image.mpr
    refine ⟨j.1, hi, ?_⟩
    cases j with
    | mk i b => simpa using hSecond

theorem lowSelected_all_negative {r : ℕ} (k : Fin r) :
    ∀ j ∈ lowSelected k, j.2 = true := by
  intro j hj
  rcases Finset.mem_image.mp hj with ⟨i, -, rfl⟩
  rfl

theorem negativePart_lowSelected {r : ℕ} (k : Fin r) :
    negativePart (lowSelected k) = lowSelected k := by
  classical
  ext j
  constructor
  · intro hj
    exact (negativePart_subset (lowSelected k)) hj
  · intro hj
    simp [negativePart, hj, lowSelected_all_negative k j hj]

theorem lowSelected_chain {r : ℕ} {k l : Fin r} (hkl : k ≤ l) :
    lowSelected k ⊆ lowSelected l := by
  intro j hj
  rcases (mem_lowSelected_iff k j).1 hj with ⟨hSecond, hlt⟩
  apply (mem_lowSelected_iff l j).2
  exact ⟨hSecond, lt_of_lt_of_le hlt hkl⟩

theorem omitted_negative_lowSelected_card {r : ℕ} (k : Fin r) :
    (negativePart (lowSelected k)ᶜ).card = r - k.val := by
  classical
  have hPartition := negativeUniverse_partition (lowSelected k)
  have hDisjoint := negativeParts_disjoint (lowSelected k)
  have hSum : r = (negativePart (lowSelected k)).card +
      (negativePart (lowSelected k)ᶜ).card := by
    calc
      r = (negativeUniverse (r := r)).card := (negativeUniverse_card (r := r)).symm
      _ = (negativePart (lowSelected k) ∪ negativePart (lowSelected k)ᶜ).card := by
        rw [← hPartition]
      _ = (negativePart (lowSelected k)).card +
          (negativePart (lowSelected k)ᶜ).card :=
        Finset.card_union_of_disjoint hDisjoint
  rw [negativePart_lowSelected, lowSelected_card] at hSum
  omega

theorem positive_not_mem_lowSelected {r : ℕ} (k i : Fin r) :
    (i, false) ∉ lowSelected k := by
  intro h
  have := (mem_lowSelected_iff k (i, false)).1 h
  simp at this

private theorem negativeAt_subset_negativePart_local {r : ℕ}
    (T : Finset (StairRel r)) (i : Fin r) :
    negativeAt T i ⊆ negativePart T := by
  intro j hj
  simp [negativeAt, negativePart] at hj ⊢
  exact ⟨hj.1, hj.2.1⟩

private def maxIndex {r : ℕ} (i k : Fin r) : Fin r :=
  ⟨max i.val k.val, max_lt i.isLt k.isLt⟩

private theorem negativeAt_lowSelected_nonempty {r : ℕ} (k i : Fin r) :
    (negativeAt (lowSelected k)ᶜ i).Nonempty := by
  classical
  let t : Fin r := maxIndex i k
  have hNotLow : (t, true) ∉ lowSelected k := by
    intro h
    rcases (mem_lowSelected_iff k (t, true)).1 h with ⟨-, hlt⟩
    dsimp [t, maxIndex] at hlt
    omega
  have hComp : (t, true) ∈ (lowSelected k)ᶜ := by simpa using hNotLow
  have hle : i ≤ t := by
    change i.val ≤ t.val
    dsimp [t, maxIndex]
    exact Nat.le_max_left _ _
  refine ⟨(t, true), ?_⟩
  simp [negativeAt, hComp, hle]

private theorem lowSelected_sum_some {r : ℕ} (k i : Fin r) :
    sumComponent (lowSelected k)ᶜ staircaseF (some i) =
      1 - (negativeAt (lowSelected k)ᶜ i).card := by
  classical
  rw [staircase_sum_formula]
  have hPos : (i, false) ∈ (lowSelected k)ᶜ := by
    simpa using positive_not_mem_lowSelected k i
  rw [if_pos hPos]

theorem lowSelected_sum_lower {r : ℕ} (k : Fin r) (a : StairAction r) :
    -((r - k.val - 1 : ℕ) : ℝ) ≤
      sumComponent (lowSelected k)ᶜ staircaseF a := by
  classical
  cases a with
  | none =>
      rw [show sumComponent (lowSelected k)ᶜ staircaseF none = 0 by
        simp [sumComponent, staircaseF]]
      exact neg_nonpos.mpr (by positivity)
  | some i =>
      rw [lowSelected_sum_some]
      have hSubset : negativeAt (lowSelected k)ᶜ i ⊆
          negativePart (lowSelected k)ᶜ :=
        negativeAt_subset_negativePart_local _ _
      have hCard := Finset.card_le_card hSubset
      rw [omitted_negative_lowSelected_card] at hCard
      have hCardR : ((negativeAt (lowSelected k)ᶜ i).card : ℝ) ≤
          ((r - k.val : ℕ) : ℝ) := by
        exact_mod_cast hCard
      have hStep : r - k.val = (r - k.val - 1) + 1 := by
        have := k.isLt
        omega
      have hStepR : ((r - k.val - 1 : ℕ) : ℝ) + 1 = ((r - k.val : ℕ) : ℝ) := by
        exact_mod_cast hStep.symm
      linarith

theorem lowSelected_sum_upper {r : ℕ} (k : Fin r) (a : StairAction r) :
    sumComponent (lowSelected k)ᶜ staircaseF a ≤ 0 := by
  classical
  cases a with
  | none => simp [sumComponent, staircaseF]
  | some i =>
      rw [lowSelected_sum_some]
      have hNonempty := negativeAt_lowSelected_nonempty k i
      have hCardR : (1 : ℝ) ≤ (negativeAt (lowSelected k)ᶜ i).card := by
        exact_mod_cast (Finset.card_pos.mpr hNonempty)
      linarith

theorem lowSelected_sum_zero_anchor {r : ℕ} (k : Fin r) :
    sumComponent (lowSelected k)ᶜ staircaseF none = 0 := by
  simp [sumComponent, staircaseF]

theorem lowSelected_sum_at_zero {r : ℕ} (k : Fin r) :
    sumComponent (lowSelected k)ᶜ staircaseF
      (some ⟨0, lt_of_le_of_lt (Nat.zero_le _) k.isLt⟩) =
      -((r - k.val - 1 : ℕ) : ℝ) := by
  classical
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  rw [lowSelected_sum_some, negativeAt_zero_eq_negativePart hr,
    omitted_negative_lowSelected_card]
  have hStep : r - k.val = (r - k.val - 1) + 1 := by
    have := k.isLt
    omega
  have hStepR : ((r - k.val - 1 : ℕ) : ℝ) + 1 = ((r - k.val : ℕ) : ℝ) := by
    exact_mod_cast hStep.symm
  linarith

theorem lowSelected_radius_exact {r : ℕ} (k : Fin r) :
    selectedRadius staircaseF (lowSelected k) =
      ((r - k.val - 1 : ℕ) : ℝ) / 2 := by
  classical
  let g : StairAction r → ℝ := sumComponent (lowSelected k)ᶜ staircaseF
  have hLower : ∀ a, -((r - k.val - 1 : ℕ) : ℝ) ≤ g a := by
    intro a
    exact lowSelected_sum_lower k a
  have hUpper : ∀ a, g a ≤ 0 := by
    intro a
    exact lowSelected_sum_upper k a
  have hAnchor : g none = 0 := lowSelected_sum_zero_anchor k
  have hAtZero : g (some ⟨0, lt_of_le_of_lt (Nat.zero_le _) k.isLt⟩) =
      -((r - k.val - 1 : ℕ) : ℝ) :=
    lowSelected_sum_at_zero k
  have hMax : maxVal g = 0 := by
    apply le_antisymm
    · exact maxVal_le _ hUpper
    · rw [← hAnchor]
      exact le_maxVal g none
  have hMin : minVal g = -((r - k.val - 1 : ℕ) : ℝ) := by
    apply le_antisymm
    · rw [← hAtZero]
      exact minVal_le g _
    · exact le_minVal _ hLower
  unfold selectedRadius supportOsc osc
  change (maxVal g - minVal g) / 2 = _
  rw [hMax, hMin]
  ring

theorem lowSelected_exact_optimal {r : ℕ} (k : Fin r) :
    EpsilonOptimalAt (selectedRadius staircaseF) 0 k.val (lowSelected k) := by
  refine ⟨lowSelected_card k, ?_⟩
  intro S hCard
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hk : k.val ≤ r - 1 := by omega
  have hLower := low_budget_radius_lower hr hk S hCard
  rw [lowSelected_radius_exact]
  linarith

/-! ## The `2r-1` boundary layer -/

theorem staircase_component_osc_one {r : ℕ} (j : StairRel r) :
    osc (staircaseF j) = 1 := by
  rcases j with ⟨i, b⟩
  cases b
  · have hMax : maxVal (staircaseF (i, false)) = 1 := by
      apply le_antisymm
      · apply maxVal_le
        intro a
        cases a with
        | none => simp [staircaseF]
        | some x => by_cases h : i = x <;> simp [staircaseF, h]
      · rw [show (1 : ℝ) = staircaseF (i, false) (some i) by simp [staircaseF]]
        exact le_maxVal _ _
    have hMin : minVal (staircaseF (i, false)) = 0 := by
      apply le_antisymm
      · calc
          minVal (staircaseF (i, false)) ≤ staircaseF (i, false) none :=
            minVal_le _ _
          _ = 0 := by simp [staircaseF]
      · apply le_minVal
        intro a
        cases a with
        | none => simp [staircaseF]
        | some x => by_cases h : i = x <;> simp [staircaseF, h]
    simp [osc, hMax, hMin]
  · have hMax : maxVal (staircaseF (i, true)) = 0 := by
      apply le_antisymm
      · apply maxVal_le
        intro a
        cases a with
        | none => simp [staircaseF]
        | some x => by_cases h : x ≤ i <;> simp [staircaseF, h]
      · rw [show (0 : ℝ) = staircaseF (i, true) none by simp [staircaseF]]
        exact le_maxVal _ _
    have hMin : minVal (staircaseF (i, true)) = -1 := by
      apply le_antisymm
      · calc
          minVal (staircaseF (i, true)) ≤ staircaseF (i, true) (some i) :=
            minVal_le _ _
          _ = -1 := by simp [staircaseF]
      · apply le_minVal
        intro a
        cases a with
        | none => simp [staircaseF]
        | some x => by_cases h : x ≤ i <;> simp [staircaseF, h]
    simp [osc, hMax, hMin]

theorem selectedRadius_compl_singleton {r : ℕ} (S : Finset (StairRel r))
    (j : StairRel r) (hCompl : Sᶜ = {j}) :
    selectedRadius staircaseF S = 1 / 2 := by
  have hSum : sumComponent ({j} : Finset (StairRel r)) staircaseF = staircaseF j := by
    funext a
    simp [sumComponent]
  unfold selectedRadius supportOsc
  rw [hCompl]
  simp [hSum, staircase_component_osc_one]

theorem card_two_mul_stairRel (r : ℕ) :
    Fintype.card (StairRel r) = 2 * r := by
  simp [StairRel, Nat.mul_comm]

/-- The hypothesis `0 < r` is not decoration: at `r = 0` the statement is FALSE.
`StairRel 0` is empty, `2 * 0 - 1 = 0` by truncated subtraction, so `S.card = 0`
holds for `S = univ = empty` and the complement has card `0`, not `1`. -/
theorem card_eq_two_mul_sub_one_radius {r : ℕ} (hr : 0 < r)
    (S : Finset (StairRel r)) (hCard : S.card = 2 * r - 1) :
    selectedRadius staircaseF S = 1 / 2 := by
  classical
  have hComplCard : Sᶜ.card = 1 := by
    have hTotal : Fintype.card (StairRel r) = 2 * r := card_two_mul_stairRel r
    have hEq : Sᶜ.card = Fintype.card (StairRel r) - S.card := by
      simpa using (Finset.card_compl S)
    rw [hEq, hTotal, hCard]
    omega
  rcases Finset.card_eq_one.mp hComplCard with ⟨j, hCompl⟩
  exact selectedRadius_compl_singleton S j hCompl

theorem high_boundary_exact_optimal {r : ℕ} (hr : 0 < r)
    (S : Finset (StairRel r)) (hCard : S.card = 2 * r - 1) :
    EpsilonOptimalAt (selectedRadius staircaseF) 0 (2 * r - 1) S := by
  refine ⟨hCard, ?_⟩
  intro T hT
  rw [card_eq_two_mul_sub_one_radius hr S hCard,
    card_eq_two_mul_sub_one_radius hr T hT]
  norm_num


/-! ## Cardinality and optimality of the zero-radius layer optima

The block `B_t` has `t+2` elements, so the retained set `staircaseSelected t`
sits at budget `2r - (t+2)`.  As `t` runs over `Fin r` those budgets are
`2r-2, 2r-3, ..., r-1`: exactly `r` layers, each with a forced unique optimum.
-/

theorem staircaseSelected_card {r : ℕ} (t : Fin r) :
    (staircaseSelected t).card = 2 * r - (t.val + 2) := by
  classical
  have h : (staircaseSelected t).card
      = Fintype.card (StairRel r) - (staircaseBlock t).card := by
    simpa [staircaseSelected] using (Finset.card_compl (staircaseBlock t))
  rw [h, card_two_mul_stairRel, staircaseBlock_card]

/-- Radius zero is the global floor, so a zero-radius set is optimal at its own
budget without any comparison argument. -/
theorem staircaseSelected_exact_optimal {r : ℕ} (t : Fin r) :
    EpsilonOptimalAt (selectedRadius (staircaseF (r := r))) 0
      (staircaseSelected t).card (staircaseSelected t) := by
  refine ⟨rfl, ?_⟩
  intro T _
  rw [staircaseSelected_radius_zero]
  have hT := selectedRadius_nonneg (staircaseF (r := r)) T
  linarith

/-! ## The low-budget family is one inclusion chain -/

def lowChain (r : ℕ) : Finset (Finset (StairRel r)) :=
  Finset.univ.image (fun k : Fin r => lowSelected k)

theorem lowChain_inclusionChain {r : ℕ} : InclusionChain (lowChain r) := by
  classical
  intro A hA B hB
  rcases Finset.mem_image.mp hA with ⟨k, -, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨l, -, rfl⟩
  rcases le_total k l with h | h
  · exact Or.inl (lowSelected_chain h)
  · exact Or.inr (lowSelected_chain h)

/-! ## The two explicit ranking families

`lowRanking` realizes the whole low chain at once -- that is the entire point
of using a chain rather than `r` separate rankings for the low budgets.  Each
`blockRanking t` realizes one zero-radius optimum.
-/

private theorem lowRanking_exists {r : ℕ} :
    ∃ ranking : List (StairRel r), IsFullRanking ranking ∧
      ∀ k : Fin r, prefixSet ranking k.val = lowSelected k := by
  classical
  rcases finite_inclusion_chain_extends_to_full_ranking (lowChain r)
      lowChain_inclusionChain with ⟨ranking, hFull, hPrefix⟩
  refine ⟨ranking, hFull, ?_⟩
  intro k
  have hmem : lowSelected k ∈ lowChain r :=
    Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  have h := hPrefix (lowSelected k) hmem
  rwa [lowSelected_card k] at h

private theorem blockRanking_exists {r : ℕ} (t : Fin r) :
    ∃ ranking : List (StairRel r), IsFullRanking ranking ∧
      prefixSet ranking (staircaseSelected t).card = staircaseSelected t := by
  classical
  have hChain : InclusionChain
      ({staircaseSelected t} : Finset (Finset (StairRel r))) := by
    intro A hA B hB
    simp only [Finset.mem_singleton] at hA hB
    subst A
    subst B
    exact Or.inl Finset.Subset.rfl
  rcases finite_inclusion_chain_extends_to_full_ranking _ hChain with
    ⟨ranking, hFull, hPrefix⟩
  exact ⟨ranking, hFull, hPrefix _ (by simp)⟩

noncomputable def lowRanking (r : ℕ) : List (StairRel r) :=
  Classical.choose (lowRanking_exists (r := r))

noncomputable def blockRanking {r : ℕ} (t : Fin r) : List (StairRel r) :=
  Classical.choose (blockRanking_exists t)

private theorem lowRanking_full {r : ℕ} : IsFullRanking (lowRanking r) :=
  (Classical.choose_spec (lowRanking_exists (r := r))).1

private theorem lowRanking_prefix {r : ℕ} (k : Fin r) :
    prefixSet (lowRanking r) k.val = lowSelected k :=
  (Classical.choose_spec (lowRanking_exists (r := r))).2 k

private theorem blockRanking_full {r : ℕ} (t : Fin r) :
    IsFullRanking (blockRanking t) :=
  (Classical.choose_spec (blockRanking_exists t)).1

private theorem blockRanking_prefix {r : ℕ} (t : Fin r) :
    prefixSet (blockRanking t) (staircaseSelected t).card = staircaseSelected t :=
  (Classical.choose_spec (blockRanking_exists t)).2

/-- The menu is indexed by `Fin r`.  The last index carries the low chain; the
other `r-1` indices carry one zero-radius optimum each.  That is why the menu
has `r` entries and not `r+1`: the low chain already covers layer `r-1`, which
is the layer `blockRanking ⟨r-1⟩` would otherwise have supplied. -/
noncomputable def stairMenuFun {r : ℕ} (t : Fin r) : List (StairRel r) :=
  if t.val + 1 = r then lowRanking r else blockRanking t

noncomputable def stairMenu (r : ℕ) : Finset (List (StairRel r)) :=
  Finset.univ.image (stairMenuFun (r := r))

theorem stairMenu_card_le {r : ℕ} : (stairMenu r).card ≤ r := by
  classical
  calc
    (stairMenu r).card ≤ (Finset.univ : Finset (Fin r)).card :=
      Finset.card_image_le
    _ = r := by simp

private theorem stairMenuFun_mem {r : ℕ} (t : Fin r) :
    stairMenuFun t ∈ stairMenu r :=
  Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩

/-! ## The covering theorem -/

theorem stairMenu_prefixCover {r : ℕ} (hr : 0 < r) :
    PrefixCover (selectedRadius (staircaseF (r := r))) 0 (stairMenu r) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hLowFull : IsFullRanking (lowRanking r) := lowRanking_full
  -- the index whose menu entry is the low chain
  let top : Fin r := ⟨r - 1, by omega⟩
  have hTopIsLow : stairMenuFun top = lowRanking r := by
    unfold stairMenuFun
    have : top.val + 1 = r := by
      show (r - 1) + 1 = r
      omega
    rw [if_pos this]
  refine ⟨Finset.image_nonempty.mpr Finset.univ_nonempty, ?_, ?_⟩
  · intro ranking hRanking
    rcases Finset.mem_image.mp hRanking with ⟨t, -, rfl⟩
    unfold stairMenuFun
    by_cases h : t.val + 1 = r
    · rw [if_pos h]
      exact hLowFull
    · rw [if_neg h]
      exact blockRanking_full t
  · intro k hk
    rw [card_two_mul_stairRel] at hk
    by_cases hLow : k < r
    · -- low chain layer
      refine ⟨stairMenuFun top, stairMenuFun_mem top, ?_⟩
      rw [hTopIsLow]
      let kk : Fin r := ⟨k, hLow⟩
      have hPrefix : prefixSet (lowRanking r) k = lowSelected kk := by
        simpa [kk] using lowRanking_prefix kk
      have hOpt := lowSelected_exact_optimal kk
      rw [hPrefix]
      simpa [kk] using hOpt
    · by_cases hMid : k ≤ 2 * r - 2
      · -- zero-radius layer, supplied by exactly one block ranking
        have hrTwo : 2 ≤ r := by omega
        let t : Fin r := ⟨2 * r - 2 - k, by omega⟩
        have hNotLow : ¬ (t.val + 1 = r) := by
          show ¬ ((2 * r - 2 - k) + 1 = r)
          omega
        have hEntry : stairMenuFun t = blockRanking t := by
          unfold stairMenuFun
          rw [if_neg hNotLow]
        have hCard : (staircaseSelected t).card = k := by
          rw [staircaseSelected_card]
          show 2 * r - ((2 * r - 2 - k) + 2) = k
          omega
        refine ⟨stairMenuFun t, stairMenuFun_mem t, ?_⟩
        rw [hEntry, ← hCard, blockRanking_prefix]
        exact staircaseSelected_exact_optimal t
      · by_cases hHigh : k = 2 * r - 1
        · -- every (2r-1)-set is optimal, so any ranking in the menu will do
          refine ⟨stairMenuFun top, stairMenuFun_mem top, ?_⟩
          rw [hTopIsLow]
          have hCard : (prefixSet (lowRanking r) k).card = k :=
            CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full
              (lowRanking r) hLowFull k (by rw [card_two_mul_stairRel]; omega)
          subst k
          exact high_boundary_exact_optimal hr _ hCard
        · -- the only remaining budget is the full ground set
          have hFullBudget : k = 2 * r := by omega
          refine ⟨stairMenuFun top, stairMenuFun_mem top, ?_⟩
          rw [hTopIsLow]
          have hCard : (prefixSet (lowRanking r) k).card = k :=
            CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full
              (lowRanking r) hLowFull k (by rw [card_two_mul_stairRel]; omega)
          have hUniv : prefixSet (lowRanking r) k = Finset.univ := by
            apply Finset.eq_univ_of_card
            rw [hCard, hFullBudget, card_two_mul_stairRel]
          refine ⟨hCard, ?_⟩
          intro T hT
          have hTUniv : T = Finset.univ := by
            apply Finset.eq_univ_of_card
            rw [hT, hFullBudget, card_two_mul_stairRel]
          rw [hUniv, hTUniv]
          linarith

/-! ## The exact law -/

theorem STRUCT_staircase_prefix_cover_at_most_r {r : ℕ} (hr : 0 < r) :
    PrefixCoverDimensionAtMost (selectedRadius (staircaseF (r := r))) 0 r :=
  ⟨stairMenu r, stairMenu_card_le, stairMenu_prefixCover hr⟩

/-- `chi_prefix(F_r, 0) = r` exactly.  The upper bound is the explicit `r`-entry
menu above; the lower bound is the compiled incomparable-optima argument. -/
theorem STRUCT_staircase_prefix_dimension_eq {r : ℕ} (hr : 0 < r) :
    prefixDimensionValue (selectedRadius (staircaseF (r := r))) 0 = r := by
  classical
  let objective : Finset (StairRel r) → ℝ := selectedRadius (staircaseF (r := r))
  have hUpperPredicate : PrefixCoverDimensionAtMost objective 0 r :=
    STRUCT_staircase_prefix_cover_at_most_r hr
  have hFeasible :
      {K : ℕ | PrefixCoverDimensionAtMost objective 0 K}.Nonempty :=
    ⟨r, hUpperPredicate⟩
  apply le_antisymm
  · exact Nat.sInf_le hUpperPredicate
  · by_contra hLower
    have hLt : prefixDimensionValue objective 0 < r := Nat.lt_of_not_ge hLower
    have hSmall : prefixDimensionValue objective 0 ≤ r - 1 :=
      Nat.le_pred_of_lt hLt
    have hMinFeasible :
        PrefixCoverDimensionAtMost objective 0
          (prefixDimensionValue objective 0) := Nat.sInf_mem hFeasible
    rcases hMinFeasible with ⟨menu, hMenuCard, hCover⟩
    exact STRUCT_UNBOUNDED_staircase_prefix_dimension_ge hr
      ⟨menu, hMenuCard.trans hSmall, hCover⟩

/-- The extremal law in ground-set terms: on this family the prefix-menu
complexity is exactly half the number of relations. -/
theorem STRUCT_staircase_chi_eq_half_ground_set {r : ℕ} (hr : 0 < r) :
    2 * prefixDimensionValue (selectedRadius (staircaseF (r := r))) 0
      = Fintype.card (StairRel r) := by
  rw [STRUCT_staircase_prefix_dimension_eq hr, card_two_mul_stairRel]


end CIGAMF.P13.StructuralStaircaseExactPrefixCover
