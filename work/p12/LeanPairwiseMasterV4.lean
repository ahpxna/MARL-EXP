import Mathlib
import «LeanSupportGeometryV4»

/-! Abstract score-interval transfer and the active operational MASTER. -/

namespace CIGAMF.V4.Pairwise

open scoped BigOperators
open SupportGeometry

variable {ι : Type*} [DecidableEq ι]

def scoreCovered (C Chat e : ι → ℝ) : Prop := ∀ j, |Chat j - C j| ≤ e j

theorem P1_sharp_swapped_score_loss
    (C Chat e : ι → ℝ) (missed added : Finset ι)
    (hcover : scoreCovered C Chat e)
    (hSwap : missed.sum Chat ≤ added.sum Chat) :
    missed.sum C - added.sum C ≤ missed.sum e + added.sum e := by
  have hm : missed.sum C ≤ missed.sum Chat + missed.sum e := by
    calc
      missed.sum C ≤ missed.sum (fun j => Chat j + e j) := by
        apply Finset.sum_le_sum
        intro j _
        have h := (abs_le.mp (hcover j)).1
        linarith
      _ = missed.sum Chat + missed.sum e := Finset.sum_add_distrib
  have ha : added.sum Chat ≤ added.sum C + added.sum e := by
    calc
      added.sum Chat ≤ added.sum (fun j => C j + e j) := by
        apply Finset.sum_le_sum
        intro j _
        have h := (abs_le.mp (hcover j)).2
        linarith
      _ = added.sum C + added.sum e := Finset.sum_add_distrib
  linarith

noncomputable def sharpGamma (e : ι → ℝ) (missed added : Finset ι) : ℝ :=
  (missed.sum e + added.sum e) / 2

theorem P1_sharp_radius_transfer
    (C Chat e : ι → ℝ) (missed added : Finset ι)
    (radiusRegret zetaDef : ℝ)
    (hcover : scoreCovered C Chat e)
    (hSwap : missed.sum Chat ≤ added.sum Chat)
    (hgeometry : radiusRegret ≤
      (missed.sum C - added.sum C) / 2 + zetaDef / 2) :
    radiusRegret ≤ sharpGamma e missed added + zetaDef / 2 := by
  have hs := P1_sharp_swapped_score_loss C Chat e missed added hcover hSwap
  unfold sharpGamma
  linarith

def lowerScore (Chat e : ι → ℝ) (j : ι) : ℝ := Chat j - e j
def upperScore (Chat e : ι → ℝ) (j : ι) : ℝ := Chat j + e j

noncomputable def operationalGamma (Chat e : ι → ℝ) (topUpper selected : Finset ι) : ℝ :=
  (topUpper.sum (upperScore Chat e) - selected.sum (lowerScore Chat e)) / 2

theorem P2_operational_retained_loss
    (C Chat e : ι → ℝ) (trueTop topUpper selected : Finset ι)
    (hTrueUpper : trueTop.sum C ≤ trueTop.sum (upperScore Chat e))
    (hUpperOptimal : trueTop.sum (upperScore Chat e) ≤
      topUpper.sum (upperScore Chat e))
    (hSelectedLower : selected.sum (lowerScore Chat e) ≤ selected.sum C) :
    (trueTop.sum C - selected.sum C) / 2 ≤
      operationalGamma Chat e topUpper selected := by
  unfold operationalGamma
  linarith

theorem P2_operational_from_score_coverage
    (C Chat e : ι → ℝ) (trueTop topUpper selected : Finset ι)
    (hcover : scoreCovered C Chat e)
    (hUpperOptimal : trueTop.sum (upperScore Chat e) ≤
      topUpper.sum (upperScore Chat e)) :
    (trueTop.sum C - selected.sum C) / 2 ≤
      operationalGamma Chat e topUpper selected := by
  apply P2_operational_retained_loss C Chat e trueTop topUpper selected
  · apply Finset.sum_le_sum
    intro j _
    have h := (abs_le.mp (hcover j)).1
    unfold upperScore
    linarith
  · exact hUpperOptimal
  · apply Finset.sum_le_sum
    intro j _
    have h := (abs_le.mp (hcover j)).2
    unfold lowerScore
    linarith

theorem ACTIVE_OPERATIONAL_MASTER
    (C Chat e : ι → ℝ) (trueTop topUpper selected : Finset ι)
    (lossSelected lossStar radiusRegret zetaDef eta : ℝ)
    (hcover : scoreCovered C Chat e)
    (hUpperOptimal : trueTop.sum (upperScore Chat e) ≤
      topUpper.sum (upperScore Chat e))
    (hgeometry : radiusRegret ≤
      (trueTop.sum C - selected.sum C) / 2 + zetaDef / 2)
    (hdownstream : lossSelected - lossStar ≤ radiusRegret + 2 * eta) :
    lossSelected - lossStar ≤
      operationalGamma Chat e topUpper selected + zetaDef / 2 + 2 * eta := by
  have hop := P2_operational_from_score_coverage C Chat e trueTop topUpper selected
    hcover hUpperOptimal
  linarith

theorem ACTIVE_OPERATIONAL_MASTER_INSTANTIATED
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι]
    (f : ι → Ω → ℝ) (Chat e : ι → ℝ)
    (trueTop topUpper selected optimum : Finset ι)
    (k : ℕ) (zetaDef eta lossSelected lossStar : ℝ)
    (hcover : scoreCovered (componentSpan f) Chat e)
    (hUpperOptimal : trueTop.sum (upperScore Chat e) ≤
      topUpper.sum (upperScore Chat e))
    (hTop : IsTopKByScore (componentSpan f) trueTop k)
    (hSelectedCard : selected.card = k) (hOptCard : optimum.card = k)
    (hZeta : deficit optimumᶜ f ≤ zetaDef)
    (hdownstream : lossSelected - lossStar ≤
      selectedRadius f selected - selectedRadius f optimum + 2 * eta) :
    lossSelected - lossStar ≤
      operationalGamma Chat e topUpper selected + zetaDef / 2 + 2 * eta := by
  have hgeometry := BH5_selected_score_to_geometry f trueTop selected optimum
    k zetaDef hTop hSelectedCard hOptCard hZeta
  have hop := P2_operational_from_score_coverage (componentSpan f) Chat e
    trueTop topUpper selected hcover hUpperOptimal
  linarith

theorem FULLY_INSTANTIATED_OPERATIONAL_MASTER
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
      operationalGamma Chat e (canonicalTopK (upperScore Chat e) k) selected +
        zetaDefFinite f k / 2 + 2 * eta := by
  have hne : (cardinalityFamily (ι := ι) k).Nonempty := by
    exact ⟨trueTop, by simp [cardinalityFamily, hTop.1]⟩
  have hUpperOptimal : trueTop.sum (upperScore Chat e) ≤
      (canonicalTopK (upperScore Chat e) k).sum (upperScore Chat e) :=
    canonicalTopK_upperOptimal (upperScore Chat e) k hne trueTop hTop.1
  have hOptComplementCard : optimumᶜ.card = Fintype.card ι - k := by
    simp [Finset.card_compl, hOptCard]
  have hZeta : deficit optimumᶜ f ≤ zetaDefFinite f k :=
    zetaDefFinite_dominates f k optimumᶜ hOptComplementCard
  have hs := (abs_le.mp (hDownstreamUniform selected hSelectedCard)).2
  have ho := (abs_le.mp (hDownstreamUniform optimum hOptCard)).1
  have hdownstream : L selected - L optimum ≤
      selectedRadius f selected - selectedRadius f optimum + 2 * eta := by
    linarith
  exact ACTIVE_OPERATIONAL_MASTER_INSTANTIATED f Chat e trueTop
    (canonicalTopK (upperScore Chat e) k) selected optimum k
    (zetaDefFinite f k) eta (L selected) (L optimum) hcover hUpperOptimal
    hTop hSelectedCard hOptCard hZeta hdownstream

def IsStrictTopK (C : ι → ℝ) (selected : Finset ι) (k : ℕ) : Prop :=
  selected.card = k ∧ ∀ j ∈ selected, ∀ l ∉ selected, C l < C j

theorem P3_exact_topk_interval_certificate
    (C Chat e : ι → ℝ) (selected : Finset ι) (k : ℕ)
    (hcover : scoreCovered C Chat e)
    (hcard : selected.card = k)
    (hseparation : ∀ j ∈ selected, ∀ l ∉ selected,
      upperScore Chat e l < lowerScore Chat e j) :
    IsStrictTopK C selected k := by
  refine ⟨hcard, ?_⟩
  intro j hj l hl
  have hjc := abs_le.mp (hcover j)
  have hlc := abs_le.mp (hcover l)
  have hsep := hseparation j hj l hl
  unfold upperScore lowerScore at hsep
  linarith

theorem exact_additive_error_instantiation
    (delta chi estimate pair primitive : ℝ)
    (hEst : |estimate - pair| ≤ delta)
    (hIso : |pair - primitive| ≤ chi) :
    |estimate - primitive| ≤ delta + chi := by
  calc
    |estimate - primitive| ≤ |estimate - pair| + |pair - primitive| := abs_sub_le _ _ _
    _ ≤ delta + chi := add_le_add hEst hIso

theorem near_additive_error_instantiation
    (delta chi rho estimate pair additivePair primitive : ℝ)
    (hEst : |estimate - pair| ≤ delta)
    (hResidual : |pair - additivePair| ≤ rho)
    (hIso : |additivePair - primitive| ≤ chi) :
    |estimate - primitive| ≤ delta + chi + rho := by
  calc
    |estimate - primitive| ≤ |estimate - pair| + |pair - additivePair| +
        |additivePair - primitive| := by
          linarith [abs_sub_le estimate pair primitive,
            abs_sub_le pair additivePair primitive]
    _ ≤ delta + rho + chi := add_le_add (add_le_add hEst hResidual) hIso
    _ = delta + chi + rho := by ring

end CIGAMF.V4.Pairwise
