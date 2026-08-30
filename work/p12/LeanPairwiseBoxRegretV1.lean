import Mathlib
import «LeanPairwiseMasterV4»

/-! Exact independent-interval-box tightening of the operational score term.

This extension imports the frozen V4 MASTER and does not modify it.  For a
fixed selected set, the adversary puts selected scores at their lower endpoints
and unselected scores at their upper endpoints. -/

namespace CIGAMF.V7.PairwiseBox

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.Pairwise

variable {ι : Type*} [DecidableEq ι]

def boxAdversaryScore
    (Chat e : ι → ℝ) (selected : Finset ι) (j : ι) : ℝ :=
  if j ∈ selected then lowerScore Chat e j else upperScore Chat e j

noncomputable def boxGamma
    [Fintype ι] (Chat e : ι → ℝ) (selected : Finset ι) (k : ℕ) : ℝ :=
  ((canonicalTopK (boxAdversaryScore Chat e selected) k).sum
      (boxAdversaryScore Chat e selected) -
    selected.sum (lowerScore Chat e)) / 2

theorem BOX1_adversary_inside_intervals
    (Chat e : ι → ℝ) (selected : Finset ι)
    (he : ∀ j, 0 ≤ e j) (j : ι) :
    lowerScore Chat e j ≤ boxAdversaryScore Chat e selected j ∧
      boxAdversaryScore Chat e selected j ≤ upperScore Chat e j := by
  by_cases hj : j ∈ selected
  · simp only [boxAdversaryScore, if_pos hj]
    constructor
    · exact le_rfl
    · unfold lowerScore upperScore
      linarith [he j]
  · simp only [boxAdversaryScore, if_neg hj]
    constructor
    · unfold lowerScore upperScore
      linarith [he j]
    · exact le_rfl

theorem BOX2_adversary_scoreCovered
    (Chat e : ι → ℝ) (selected : Finset ι)
    (he : ∀ j, 0 ≤ e j) :
    scoreCovered (boxAdversaryScore Chat e selected) Chat e := by
  intro j
  have h := BOX1_adversary_inside_intervals Chat e selected he j
  unfold lowerScore upperScore at h
  exact abs_le.mpr ⟨by linarith [h.2], by linarith [h.1]⟩

private theorem retained_score_cancellation
    (C : ι → ℝ) (trueTop selected : Finset ι) :
    trueTop.sum C - selected.sum C =
      (trueTop \ selected).sum C - (selected \ trueTop).sum C := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff]

theorem BOX3_retained_loss_le_boxGamma
    [Fintype ι]
    (C Chat e : ι → ℝ) (trueTop selected : Finset ι) (k : ℕ)
    (hcover : scoreCovered C Chat e)
    (hTrueTop : IsTopKByScore C trueTop k)
    (hSelectedCard : selected.card = k) :
    (trueTop.sum C - selected.sum C) / 2 ≤
      boxGamma Chat e selected k := by
  let Cadv := boxAdversaryScore Chat e selected
  have hMissed : (trueTop \ selected).sum C ≤
      (trueTop \ selected).sum Cadv := by
    apply Finset.sum_le_sum
    intro j hj
    have hjNot : j ∉ selected := (Finset.mem_sdiff.mp hj).2
    have hc := (abs_le.mp (hcover j)).1
    simp only [Cadv, boxAdversaryScore, if_neg hjNot, upperScore]
    linarith
  have hAdded : (selected \ trueTop).sum Cadv ≤
      (selected \ trueTop).sum C := by
    apply Finset.sum_le_sum
    intro j hj
    have hjSel : j ∈ selected := (Finset.mem_sdiff.mp hj).1
    have hc := (abs_le.mp (hcover j)).2
    simp only [Cadv, boxAdversaryScore, if_pos hjSel, lowerScore]
    linarith
  have hCancellationAdv :
      (trueTop \ selected).sum Cadv - (selected \ trueTop).sum Cadv =
        trueTop.sum Cadv - selected.sum Cadv := by
    exact (retained_score_cancellation Cadv trueTop selected).symm
  have hSelectedAdv : selected.sum Cadv = selected.sum (lowerScore Chat e) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Cadv, boxAdversaryScore, hj]
  have hne : (cardinalityFamily (ι := ι) k).Nonempty := by
    exact ⟨trueTop, by simp [cardinalityFamily, hTrueTop.1]⟩
  have hTopAdv : trueTop.sum Cadv ≤ (canonicalTopK Cadv k).sum Cadv :=
    canonicalTopK_upperOptimal Cadv k hne trueTop hTrueTop.1
  have hDiffAdv :
      (trueTop \ selected).sum C - (selected \ trueTop).sum C ≤
        trueTop.sum Cadv - selected.sum Cadv := by
    rw [← hCancellationAdv]
    linarith
  rw [retained_score_cancellation C trueTop selected]
  unfold boxGamma
  change ((trueTop \ selected).sum C - (selected \ trueTop).sum C) / 2 ≤
    ((canonicalTopK Cadv k).sum Cadv - selected.sum (lowerScore Chat e)) / 2
  rw [← hSelectedAdv]
  linarith

theorem BOX4_boxGamma_attained
    [Fintype ι]
    (Chat e : ι → ℝ) (selected : Finset ι) (k : ℕ) :
    let Cadv := boxAdversaryScore Chat e selected
    let Tadv := canonicalTopK Cadv k
    (Tadv.sum Cadv - selected.sum Cadv) / 2 =
      boxGamma Chat e selected k := by
  dsimp
  unfold boxGamma
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  simp [boxAdversaryScore, hj]

theorem BOX5_boxGamma_le_operationalGamma
    [Fintype ι]
    (Chat e : ι → ℝ) (selected : Finset ι) (k : ℕ)
    (he : ∀ j, 0 ≤ e j)
    (hSelectedCard : selected.card = k) :
    boxGamma Chat e selected k ≤
      operationalGamma Chat e
        (canonicalTopK (upperScore Chat e) k) selected := by
  let Cadv := boxAdversaryScore Chat e selected
  let Tadv := canonicalTopK Cadv k
  have hne : (cardinalityFamily (ι := ι) k).Nonempty := by
    exact ⟨selected, by simp [cardinalityFamily, hSelectedCard]⟩
  have hTadvCard : Tadv.card = k := (canonicalTopK_spec Cadv k hne).1
  have hPointwise : ∀ j, Cadv j ≤ upperScore Chat e j := by
    intro j
    exact (BOX1_adversary_inside_intervals Chat e selected he j).2
  have hFirst : Tadv.sum Cadv ≤ Tadv.sum (upperScore Chat e) := by
    exact Finset.sum_le_sum (fun j _ => hPointwise j)
  have hSecond : Tadv.sum (upperScore Chat e) ≤
      (canonicalTopK (upperScore Chat e) k).sum (upperScore Chat e) :=
    canonicalTopK_upperOptimal (upperScore Chat e) k hne Tadv hTadvCard
  unfold boxGamma operationalGamma
  change (Tadv.sum Cadv - selected.sum (lowerScore Chat e)) / 2 ≤
    ((canonicalTopK (upperScore Chat e) k).sum (upperScore Chat e) -
      selected.sum (lowerScore Chat e)) / 2
  linarith

theorem BOX5b_boxGamma_eq_operationalGamma_of_selected_zero_error
    [Fintype ι]
    (Chat e : ι → ℝ) (selected : Finset ι) (k : ℕ)
    (hzero : ∀ j ∈ selected, e j = 0) :
    boxGamma Chat e selected k =
      operationalGamma Chat e
        (canonicalTopK (upperScore Chat e) k) selected := by
  have hscore : boxAdversaryScore Chat e selected = upperScore Chat e := by
    funext j
    by_cases hj : j ∈ selected
    · simp [boxAdversaryScore, hj, lowerScore, upperScore, hzero j hj]
    · simp [boxAdversaryScore, hj]
  unfold boxGamma operationalGamma
  rw [hscore]

def boxWitnessChat (_ : Fin 3) : ℝ := 0

def boxWitnessError (j : Fin 3) : ℝ := if j = 0 then 2 else 0

def boxWitnessSelected : Finset (Fin 3) := {0}

theorem boxWitness_upper_top_sum :
    (canonicalTopK (upperScore boxWitnessChat boxWitnessError) 1).sum
      (upperScore boxWitnessChat boxWitnessError) = 2 := by
  have hne : (cardinalityFamily (ι := Fin 3) 1).Nonempty := by
    exact ⟨{0}, by simp [cardinalityFamily]⟩
  have hspec := canonicalTopK_spec
    (upperScore boxWitnessChat boxWitnessError) 1 hne
  have hUpper := hspec.2 ({0} : Finset (Fin 3)) (by simp)
  have hBound : ∀ j : Fin 3, upperScore boxWitnessChat boxWitnessError j ≤ 2 := by
    intro j
    fin_cases j <;> simp [upperScore, boxWitnessChat, boxWitnessError]
  have hsumBound :
      (canonicalTopK (upperScore boxWitnessChat boxWitnessError) 1).sum
        (upperScore boxWitnessChat boxWitnessError) ≤ 2 := by
    calc
      _ ≤ (canonicalTopK (upperScore boxWitnessChat boxWitnessError) 1).sum
          (fun _ => (2 : ℝ)) := Finset.sum_le_sum (fun j _ => hBound j)
      _ = 2 := by simp [hspec.1]
  have hzero : ({0} : Finset (Fin 3)).sum
      (upperScore boxWitnessChat boxWitnessError) = 2 := by
    simp [upperScore, boxWitnessChat, boxWitnessError]
  rw [hzero] at hUpper
  linarith

theorem boxWitness_adversary_top_sum :
    (canonicalTopK
      (boxAdversaryScore boxWitnessChat boxWitnessError boxWitnessSelected) 1).sum
      (boxAdversaryScore boxWitnessChat boxWitnessError boxWitnessSelected) = 0 := by
  have hne : (cardinalityFamily (ι := Fin 3) 1).Nonempty := by
    exact ⟨{1}, by simp [cardinalityFamily]⟩
  have hspec := canonicalTopK_spec
    (boxAdversaryScore boxWitnessChat boxWitnessError boxWitnessSelected) 1 hne
  have hLower := hspec.2 ({1} : Finset (Fin 3)) (by simp)
  have hBound : ∀ j : Fin 3,
      boxAdversaryScore boxWitnessChat boxWitnessError boxWitnessSelected j ≤ 0 := by
    intro j
    fin_cases j <;>
      simp [boxAdversaryScore, boxWitnessChat, boxWitnessError, boxWitnessSelected,
        lowerScore, upperScore]
  have hsumBound :
      (canonicalTopK
        (boxAdversaryScore boxWitnessChat boxWitnessError boxWitnessSelected) 1).sum
        (boxAdversaryScore boxWitnessChat boxWitnessError boxWitnessSelected) ≤ 0 := by
    calc
      _ ≤ (canonicalTopK
          (boxAdversaryScore boxWitnessChat boxWitnessError boxWitnessSelected) 1).sum
          (fun _ => (0 : ℝ)) := Finset.sum_le_sum (fun j _ => hBound j)
      _ = 0 := by simp
  have hone : ({1} : Finset (Fin 3)).sum
      (boxAdversaryScore boxWitnessChat boxWitnessError boxWitnessSelected) = 0 := by
    simp [boxAdversaryScore, boxWitnessChat, boxWitnessError, boxWitnessSelected,
      lowerScore, upperScore]
  rw [hone] at hLower
  linarith

theorem BOX6_strict_tightening_witness :
    boxGamma boxWitnessChat boxWitnessError boxWitnessSelected 1 <
      operationalGamma boxWitnessChat boxWitnessError
        (canonicalTopK (upperScore boxWitnessChat boxWitnessError) 1)
        boxWitnessSelected := by
  rw [show boxGamma boxWitnessChat boxWitnessError boxWitnessSelected 1 = 1 by
      unfold boxGamma
      rw [boxWitness_adversary_top_sum]
      norm_num [boxWitnessSelected, lowerScore, boxWitnessChat, boxWitnessError],
    show operationalGamma boxWitnessChat boxWitnessError
        (canonicalTopK (upperScore boxWitnessChat boxWitnessError) 1)
        boxWitnessSelected = 2 by
      unfold operationalGamma
      rw [boxWitness_upper_top_sum]
      norm_num [boxWitnessSelected, lowerScore, boxWitnessChat, boxWitnessError]]
  norm_num

theorem BOX7_FULLY_INSTANTIATED_OPERATIONAL_MASTER
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι]
    (f : ι → Ω → ℝ) (Chat e : ι → ℝ) (L : Finset ι → ℝ)
    (trueTop selected optimum : Finset ι)
    (k : ℕ) (eta : ℝ)
    (hcover : scoreCovered (componentSpan f) Chat e)
    (hTop : IsTopKByScore (componentSpan f) trueTop k)
    (hSelectedCard : selected.card = k) (hOptCard : optimum.card = k)
    (hDownstreamUniform : ∀ S : Finset ι, S.card = k →
      |L S - selectedRadius f S| ≤ eta) :
    L selected - L optimum ≤
      boxGamma Chat e selected k + zetaDefFinite f k / 2 + 2 * eta := by
  have hOptComplementCard : optimumᶜ.card = Fintype.card ι - k := by
    simp [Finset.card_compl, hOptCard]
  have hZeta : deficit optimumᶜ f ≤ zetaDefFinite f k :=
    zetaDefFinite_dominates f k optimumᶜ hOptComplementCard
  have hgeometry := BH5_selected_score_to_geometry f trueTop selected optimum
    k (zetaDefFinite f k) hTop hSelectedCard hOptCard hZeta
  have hbox := BOX3_retained_loss_le_boxGamma (componentSpan f) Chat e
    trueTop selected k hcover hTop hSelectedCard
  have hs := (abs_le.mp (hDownstreamUniform selected hSelectedCard)).2
  have ho := (abs_le.mp (hDownstreamUniform optimum hOptCard)).1
  have hdownstream : L selected - L optimum ≤
      selectedRadius f selected - selectedRadius f optimum + 2 * eta := by
    linarith
  linarith

end CIGAMF.V7.PairwiseBox
