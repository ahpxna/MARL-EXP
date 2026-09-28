import Mathlib
import «LeanD6BinaryIntegerCounterexampleV1»
import «LeanD6ContrastRankPhaseDefinitionsV2»
import «LeanD6PolyhedralActiveCellV1»
import «LeanD6RawLocalContrastRankOneV1»

/-!
# Bridge: the integer binary counterexample, in the chain's own vocabulary

`LeanD6BinaryIntegerCounterexampleV1` proves eighteen arithmetic facts about its
own definitions (`Wf`, `resp`, `osc6`, `gSel`, `gCom`, `rho_i`).  Those are not
yet statements about D6: the identification of `gSel` with `retainedResidual`, of
`osc6` with `osc (productResponse …)`, and of the pair `(86, 85)` with
`2 (ℓ_S − ℓ_T)` and `(m−1) δ□` rested on prose.  This file discharges exactly
that identification, and then states the refutation in the phase language.

Two facts make the bridge much lighter than the K = 3 case of
`LeanD6StrictTwoProfileRankOneM6CounterexampleV2`:

* `Wf 0 0 0 0 0 0 = 0`, so `resp i 0 = 0` and the corner-referenced additive
  component IS the response.  `retainedResidual` therefore coincides with
  `gSel` / `gCom` with no baseline term.
* at `|U| = 2` every identification is a statement over a finite decidable type,
  so it is discharged by `decide` at the `ℤ` / `Fin` level.  Only the final
  rescale by `1/17` happens over `ℝ`.

The refuted statement is the plain decision bound.  No rank hypothesis is used:
at `|U| = 2` the rank-one hypotheses hold for every world, which is why the
corollary at the end costs nothing.
-/

namespace CIGAMF.P13.D6BinaryBridgeV1

set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6H3Exchange
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6PolyhedralActiveCell
open CIGAMF.P13.D6DecisionInteractionComplexity
open CIGAMF.P13.D6ContrastRankPhaseDefinitionsV2
open CIGAMF.P13.D6BinaryIntegerCounterexampleV1
open CIGAMF.P13.D6RawLocalContrastRankOne

/-! ## The corner reference on `Fin 2` -/

def z6 : Fin 6 → Fin 2 := fun _ => 0

def cornerQ2 (_i : Fin 6) (u : Fin 2) : ℝ := if u = 0 then 1 else 0

theorem cornerQ2_nonnegative (c : Fin 6 → Fin 2) : 0 ≤ jointWeight cornerQ2 c := by
  unfold jointWeight
  apply Finset.prod_nonneg
  intro i _
  unfold cornerQ2
  split <;> norm_num

theorem cornerQ2_jointWeight (c : Fin 6 → Fin 2) :
    jointWeight cornerQ2 c = if c = z6 then 1 else 0 := by
  unfold jointWeight cornerQ2
  by_cases h : c = z6
  · subst h
    simp [z6]
  · rw [if_neg h]
    have : ∃ i, c i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h (funext fun i => hc i)
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem cornerQ2_normalized : ∑ c, jointWeight cornerQ2 c = 1 := by
  simp [cornerQ2_jointWeight]

theorem cornerQ2_expectation (G : (Fin 6 → Fin 2) → ℝ) :
    productExpectation cornerQ2 G = G z6 := by
  unfold productExpectation
  simp [cornerQ2_jointWeight]

theorem cornerQ2_response (F : (Fin 6 → Fin 2) → ℝ) (i : Fin 6) (u : Fin 2) :
    productResponse cornerQ2 F i u = F (Function.update z6 i u) := by
  unfold productResponse
  rw [cornerQ2_expectation]

/-! ## The world -/

/-- The rescaled world.  `δ□ = 17` for `rawWorld`, so dividing by `17` is exactly
the unit-interaction normalisation, not a slack one. -/
noncomputable def Wr (x : Fin 6 → Fin 2) : ℝ := (rawWorld x : ℝ) / 17

theorem Wr_apply (x : Fin 6 → Fin 2) : Wr x = (rawWorld x : ℝ) / 17 := rfl

/-! ## Identifications at the integer level

Each of these is a statement over a finite decidable type, so `decide` settles
it; nothing here is a claim about `ℝ`. -/

/-- The response of coordinate `i` at symbol `u` is the world at the corner with
`u` inserted, which is exactly `resp`. -/
theorem rawWorld_update_eq_resp (i : Fin 6) (u : Fin 2) :
    rawWorld (Function.update z6 i u) = resp i u := by
  fin_cases i <;> fin_cases u <;>
    simp [rawWorld, resp, z6, Function.update_apply, Fin.ext_iff] <;> rfl

/-- The corner reference is anchored: `resp i 0 = 0` for every `i`, so the
additive component equals the response. -/
theorem resp_zero : ∀ i : Fin 6, resp i 0 = 0 := by decide

theorem comp_eq_resp : ∀ (i : Fin 6) (u : Fin 2), comp i u = resp i u := by decide

def selected2 : Finset (Fin 6) := {0, 4, 5}
def competitor2 : Finset (Fin 6) := {1, 2, 3}

/-! ## Discipline: never `decide` over a function type

`decide` on `∀ z : Fin 6 → Fin 2, …` forces Lean to build the `Fintype` instance
for a PI type and the kernel then reduces a term of enormous size; the first
version of this file exhausted 64 GB on exactly that.  Every finite check below
is therefore stated over SIX EXPLICIT `Fin 2` arguments, which is how the base
module `LeanD6BinaryIntegerCounterexampleV1` compiles in seconds, and lifted to
functions by the eta lemma. -/

private theorem fin6_eta (z : Fin 6 → Fin 2) : z = ![z 0, z 1, z 2, z 3, z 4, z 5] := by
  funext j; fin_cases j <;> rfl

private theorem forall_fin6 {P : (Fin 6 → Fin 2) → Prop}
    (h : ∀ a b c d e f : Fin 2, P ![a, b, c, d, e, f]) (z : Fin 6 → Fin 2) : P z := by
  rw [fin6_eta z]; exact h _ _ _ _ _ _

/-- The two retained sums, written out.  Keeping `Finset.sum` inside a `decide`
is another way to make the kernel work far harder than it needs to. -/
private theorem sum_selected (z : Fin 6 → Fin 2) :
    ∑ j ∈ selected2, resp j (z j) = resp 0 (z 0) + resp 4 (z 4) + resp 5 (z 5) := by
  simp [selected2, Finset.sum_insert, Finset.mem_insert]
  ring

private theorem sum_competitor (z : Fin 6 → Fin 2) :
    ∑ j ∈ competitor2, resp j (z j) = resp 1 (z 1) + resp 2 (z 2) + resp 3 (z 3) := by
  simp [competitor2, Finset.sum_insert, Finset.mem_insert]
  ring


/-- `gSel` is the retained residual of the selected set, as an integer. -/
theorem gSel_eq_residual (z : Fin 6 → Fin 2) :
    gSel (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) =
      rawWorld z - ∑ j ∈ selected2, resp j (z j) := by
  rw [sum_selected]
  revert z
  refine forall_fin6 ?_
  decide

theorem gCom_eq_residual (z : Fin 6 → Fin 2) :
    gCom (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) =
      rawWorld z - ∑ j ∈ competitor2, resp j (z j) := by
  rw [sum_competitor]
  revert z
  refine forall_fin6 ?_
  decide

/-! ### The mixed-difference bound `δ□ = 17`

Not decided over function types.  For each coordinate the second difference is
stated over TWELVE explicit `Fin 2` arguments -- the two symbols at that
coordinate and the two five-symbol contexts -- giving `4096` integer cases per
coordinate.  That is four times the work of `rho_spreads_le_seventeen` in the
base module, which compiles in seconds; deciding the same fact over
`Fin 6 → Fin 2` instead is `6 · 64 · 64` cases over a PI type and exhausts
memory. -/

theorem md0 : ∀ u v b c d e f b' c' d' e' f' : Fin 2,
    |(Wf u b c d e f - Wf v b c d e f) - (Wf u b' c' d' e' f' - Wf v b' c' d' e' f')| ≤ 17 := by
  decide

theorem md1 : ∀ u v a c d e f a' c' d' e' f' : Fin 2,
    |(Wf a u c d e f - Wf a v c d e f) - (Wf a' u c' d' e' f' - Wf a' v c' d' e' f')| ≤ 17 := by
  decide

theorem md2 : ∀ u v a b d e f a' b' d' e' f' : Fin 2,
    |(Wf a b u d e f - Wf a b v d e f) - (Wf a' b' u d' e' f' - Wf a' b' v d' e' f')| ≤ 17 := by
  decide

theorem md3 : ∀ u v a b c e f a' b' c' e' f' : Fin 2,
    |(Wf a b c u e f - Wf a b c v e f) - (Wf a' b' c' u e' f' - Wf a' b' c' v e' f')| ≤ 17 := by
  decide

theorem md4 : ∀ u v a b c d f a' b' c' d' f' : Fin 2,
    |(Wf a b c d u f - Wf a b c d v f) - (Wf a' b' c' d' u f' - Wf a' b' c' d' v f')| ≤ 17 := by
  decide

theorem md5 : ∀ u v a b c d e a' b' c' d' e' : Fin 2,
    |(Wf a b c d e u - Wf a b c d e v) - (Wf a' b' c' d' e' u - Wf a' b' c' d' e' v)| ≤ 17 := by
  decide

/-- Lift to the chain's `mixedDifference` shape.  After `fin6_eta` and
`Function.update_apply` every term is `Wf` at an explicit tuple, so each of the
six coordinates matches one of `md0 … md5` verbatim. -/
theorem rawWorld_mixed_le_seventeen (i : Fin 6) (x c : Fin 6 → Fin 2) :
    |rawWorld x - rawWorld (Function.update x i (c i)) -
      rawWorld (Function.update c i (x i)) + rawWorld c| ≤ 17 := by
  have hx := fin6_eta x
  have hc := fin6_eta c
  fin_cases i <;>
    simp [rawWorld, Function.update_apply, Fin.ext_iff] <;>
    [ (have := md0 (x 0) (c 0) (x 1) (x 2) (x 3) (x 4) (x 5) (c 1) (c 2) (c 3) (c 4) (c 5)) ;
      (have := md1 (x 1) (c 1) (x 0) (x 2) (x 3) (x 4) (x 5) (c 0) (c 2) (c 3) (c 4) (c 5)) ;
      (have := md2 (x 2) (c 2) (x 0) (x 1) (x 3) (x 4) (x 5) (c 0) (c 1) (c 3) (c 4) (c 5)) ;
      (have := md3 (x 3) (c 3) (x 0) (x 1) (x 2) (x 4) (x 5) (c 0) (c 1) (c 2) (c 4) (c 5)) ;
      (have := md4 (x 4) (c 4) (x 0) (x 1) (x 2) (x 3) (x 5) (c 0) (c 1) (c 2) (c 3) (c 5)) ;
      (have := md5 (x 5) (c 5) (x 0) (x 1) (x 2) (x 3) (x 4) (c 0) (c 1) (c 2) (c 3) (c 4)) ] <;>
    first
      | exact this
      | (rw [abs_le] at this ⊢; omega)
      | (rw [abs_le] at this ⊢; constructor <;> linarith)

/-! ## Extremal points of the two residuals -/

def selMax : Fin 6 → Fin 2 := ![0, 1, 1, 0, 0, 0]
def selMin : Fin 6 → Fin 2 := ![1, 0, 0, 1, 1, 1]
def comMax : Fin 6 → Fin 2 := ![1, 0, 0, 0, 0, 0]
def comMin : Fin 6 → Fin 2 := z6
def respMax : Fin 6 → Fin 2 := ![1, 1, 1, 0, 1, 1]
def respMin : Fin 6 → Fin 2 := ![0, 0, 0, 1, 0, 0]

theorem residual_selected_bounds (z : Fin 6 → Fin 2) :
    (rawWorld selMin - ∑ j ∈ selected2, resp j (selMin j) ≤
        rawWorld z - ∑ j ∈ selected2, resp j (z j)) ∧
    (rawWorld z - ∑ j ∈ selected2, resp j (z j) ≤
        rawWorld selMax - ∑ j ∈ selected2, resp j (selMax j)) := by
  rw [sum_selected, sum_selected, sum_selected]
  revert z
  refine forall_fin6 ?_
  decide

theorem residual_competitor_bounds (z : Fin 6 → Fin 2) :
    (rawWorld comMin - ∑ j ∈ competitor2, resp j (comMin j) ≤
        rawWorld z - ∑ j ∈ competitor2, resp j (z j)) ∧
    (rawWorld z - ∑ j ∈ competitor2, resp j (z j) ≤
        rawWorld comMax - ∑ j ∈ competitor2, resp j (comMax j)) := by
  rw [sum_competitor, sum_competitor, sum_competitor]
  revert z
  refine forall_fin6 ?_
  decide

theorem residual_selected_values :
    rawWorld selMax - ∑ j ∈ selected2, resp j (selMax j) = 42 ∧
    rawWorld selMin - ∑ j ∈ selected2, resp j (selMin j) = -59 := by
  rw [sum_selected, sum_selected]
  constructor <;> decide

theorem residual_competitor_values :
    rawWorld comMax - ∑ j ∈ competitor2, resp j (comMax j) = 15 ∧
    rawWorld comMin - ∑ j ∈ competitor2, resp j (comMin j) = 0 := by
  rw [sum_competitor, sum_competitor]
  constructor <;> decide

theorem response_extremes : ∀ (i : Fin 6) (u : Fin 2),
    resp i u ≤ resp i (respMax i) ∧ resp i (respMin i) ≤ resp i u := by decide

/-- Strict Top-3 with integer margin `1`: the selection is geometry, not a
tie-break. -/
theorem strict_topC_integer : ∀ i ∈ selected2, ∀ j ∉ selected2,
    resp j (respMax j) - resp j (respMin j) <
      resp i (respMax i) - resp i (respMin i) := by decide

/-! ## Lifting to the chain vocabulary over `ℝ`

Every goal below has the shape `a / 17 ≤ b / 17` or `a / 17 < b / 17` with `a`,
`b` integers already compared in Part A.  Rather than chase Mathlib's division
lemma names, the two helpers `div17_le` / `div17_lt` discharge all of them
through `linarith`, for which division by a numeral is linear. -/

private theorem div17_le {a b : ℤ} (h : a ≤ b) : (a : ℝ) / 17 ≤ (b : ℝ) / 17 := by
  have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
  linarith

private theorem div17_lt {a b : ℤ} (h : a < b) : (a : ℝ) / 17 < (b : ℝ) / 17 := by
  have : (a : ℝ) < (b : ℝ) := by exact_mod_cast h
  linarith

theorem Wr_response (i : Fin 6) (u : Fin 2) :
    productResponse cornerQ2 Wr i u = (resp i u : ℝ) / 17 := by
  rw [cornerQ2_response, Wr_apply, rawWorld_update_eq_resp]

theorem Wr_retained_selected (z : Fin 6 → Fin 2) :
    retainedResidual cornerQ2 Wr selected2 z =
      ((rawWorld z - ∑ j ∈ selected2, resp j (z j) : ℤ) : ℝ) / 17 := by
  unfold retainedResidual
  simp only [Wr_apply, Wr_response]
  push_cast
  rw [← Finset.sum_div, ← sub_div]

theorem Wr_retained_competitor (z : Fin 6 → Fin 2) :
    retainedResidual cornerQ2 Wr competitor2 z =
      ((rawWorld z - ∑ j ∈ competitor2, resp j (z j) : ℤ) : ℝ) / 17 := by
  unfold retainedResidual
  simp only [Wr_apply, Wr_response]
  push_cast
  rw [← Finset.sum_div, ← sub_div]

/-- The four residual extremes as explicit reals; stated once so that no `rw`
ever has to match an integer literal against a real one. -/
theorem retained_sel_max_val :
    retainedResidual cornerQ2 Wr selected2 selMax = (42 : ℝ) / 17 := by
  rw [Wr_retained_selected, residual_selected_values.1]; norm_num

theorem retained_sel_min_val :
    retainedResidual cornerQ2 Wr selected2 selMin = (-59 : ℝ) / 17 := by
  rw [Wr_retained_selected, residual_selected_values.2]; norm_num

theorem retained_com_max_val :
    retainedResidual cornerQ2 Wr competitor2 comMax = (15 : ℝ) / 17 := by
  rw [Wr_retained_competitor, residual_competitor_values.1]; norm_num

theorem retained_com_min_val :
    retainedResidual cornerQ2 Wr competitor2 comMin = (0 : ℝ) / 17 := by
  rw [Wr_retained_competitor, residual_competitor_values.2]; norm_num

theorem Wr_unitInteraction : UnitInteractionBound Wr := by
  intro i x c
  have h := rawWorld_mixed_le_seventeen i x c
  unfold mixedDifference
  simp only [Wr_apply]
  have hcast : (rawWorld x : ℝ) / 17 - (rawWorld (Function.update x i (c i)) : ℝ) / 17 -
      (rawWorld (Function.update c i (x i)) : ℝ) / 17 + (rawWorld c : ℝ) / 17 =
      ((rawWorld x - rawWorld (Function.update x i (c i)) -
        rawWorld (Function.update c i (x i)) + rawWorld c : ℤ) : ℝ) / 17 := by
    push_cast; ring
  rw [hcast, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 17),
    div_le_one (by norm_num : (0:ℝ) < 17), ← Int.cast_abs]
  exact_mod_cast h

/-! ## The active decision cell -/

def witnessCell2 : ActiveDecisionCell 5 (Fin 2) where
  q := cornerQ2
  selected := selected2
  competitor := competitor2
  selectedMax := selMax
  selectedMin := selMin
  competitorMax := comMax
  competitorMin := comMin
  responseMax := respMax
  responseMin := respMin

theorem witness2_balanced : witnessCell2.BalancedComplement := by
  refine ⟨by decide, ?_, ?_⟩ <;> decide

/-- `responseWitnessSpan` is the difference of two responses, so it inherits the
integer span directly.  This is the quantity the polyhedral form compares, not
`osc`; conflating the two was a defect in the first version of this file. -/
theorem span_eq (j : Fin 6) :
    responseWitnessSpan witnessCell2 Wr j =
      ((resp j (respMax j) - resp j (respMin j) : ℤ) : ℝ) / 17 := by
  show productResponse cornerQ2 Wr j (respMax j) -
    productResponse cornerQ2 Wr j (respMin j) = _
  simp only [Wr_response]
  push_cast
  ring

theorem witness2_cell_valid : witnessCell2.Valid Wr := by
  rw [activeDecisionCell_valid_iff_polyhedral]
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    show retainedResidual cornerQ2 Wr selected2 z ≤
      retainedResidual cornerQ2 Wr selected2 selMax
    rw [Wr_retained_selected, Wr_retained_selected]
    exact div17_le (residual_selected_bounds z).2
  · intro z
    show retainedResidual cornerQ2 Wr selected2 selMin ≤
      retainedResidual cornerQ2 Wr selected2 z
    rw [Wr_retained_selected, Wr_retained_selected]
    exact div17_le (residual_selected_bounds z).1
  · intro z
    show retainedResidual cornerQ2 Wr competitor2 z ≤
      retainedResidual cornerQ2 Wr competitor2 comMax
    rw [Wr_retained_competitor, Wr_retained_competitor]
    exact div17_le (residual_competitor_bounds z).2
  · intro z
    show retainedResidual cornerQ2 Wr competitor2 comMin ≤
      retainedResidual cornerQ2 Wr competitor2 z
    rw [Wr_retained_competitor, Wr_retained_competitor]
    exact div17_le (residual_competitor_bounds z).1
  · intro j u
    show productResponse cornerQ2 Wr j u ≤ productResponse cornerQ2 Wr j (respMax j)
    rw [Wr_response, Wr_response]
    exact div17_le (response_extremes j u).1
  · intro j u
    show productResponse cornerQ2 Wr j (respMin j) ≤ productResponse cornerQ2 Wr j u
    rw [Wr_response, Wr_response]
    exact div17_le (response_extremes j u).2
  · intro i hi j hj
    rw [span_eq, span_eq]
    exact (div17_lt (strict_topC_integer i hi j hj)).le

/-- `StrictTopC` is phrased with `osc`, so it needs the response extremes to
identify `osc` with the span; that is the only place `maxVal` / `minVal` enter. -/
theorem witness2_strictTopC : StrictTopC witnessCell2 Wr := by
  have hosc : ∀ k : Fin 6, osc (productResponse cornerQ2 Wr k) =
      ((resp k (respMax k) - resp k (respMin k) : ℤ) : ℝ) / 17 := by
    intro k
    have hmax : maxVal (productResponse cornerQ2 Wr k) = (resp k (respMax k) : ℝ) / 17 := by
      refine le_antisymm (maxVal_le _ ?_) ?_
      · intro u
        rw [Wr_response]
        exact div17_le (response_extremes k u).1
      · rw [← Wr_response]
        exact le_maxVal _ _
    have hmin : minVal (productResponse cornerQ2 Wr k) = (resp k (respMin k) : ℝ) / 17 := by
      refine le_antisymm ?_ (le_minVal _ ?_)
      · rw [← Wr_response]
        exact minVal_le _ _
      · intro u
        rw [Wr_response]
        exact div17_le (response_extremes k u).2
    unfold osc
    rw [hmax, hmin]
    push_cast
    ring
  intro i hi j hj
  show osc (productResponse cornerQ2 Wr j) < osc (productResponse cornerQ2 Wr i)
  rw [hosc i, hosc j]
  exact div17_lt (strict_topC_integer i hi j hj)

/-! ## The doubled decision gap, and the refutation -/

theorem witness2_doubled_gap :
    2 * (productCompressionLoss Wr (productResponse cornerQ2 Wr) selected2 -
      productCompressionLoss Wr (productResponse cornerQ2 Wr) competitor2) = 86 / 17 := by
  have hS : osc (retainedResidual cornerQ2 Wr selected2) = 101 / 17 := by
    have hmax : maxVal (retainedResidual cornerQ2 Wr selected2) = (42 : ℝ) / 17 := by
      refine le_antisymm (maxVal_le _ ?_) ?_
      · intro z
        rw [Wr_retained_selected, ← retained_sel_max_val, Wr_retained_selected]
        exact div17_le (residual_selected_bounds z).2
      · rw [← retained_sel_max_val]
        exact le_maxVal _ _
    have hmin : minVal (retainedResidual cornerQ2 Wr selected2) = (-59 : ℝ) / 17 := by
      refine le_antisymm ?_ (le_minVal _ ?_)
      · rw [← retained_sel_min_val]
        exact minVal_le _ _
      · intro z
        rw [Wr_retained_selected, ← retained_sel_min_val, Wr_retained_selected]
        exact div17_le (residual_selected_bounds z).1
    unfold osc; rw [hmax, hmin]; ring
  have hT : osc (retainedResidual cornerQ2 Wr competitor2) = 15 / 17 := by
    have hmax : maxVal (retainedResidual cornerQ2 Wr competitor2) = (15 : ℝ) / 17 := by
      refine le_antisymm (maxVal_le _ ?_) ?_
      · intro z
        rw [Wr_retained_competitor, ← retained_com_max_val, Wr_retained_competitor]
        exact div17_le (residual_competitor_bounds z).2
      · rw [← retained_com_max_val]
        exact le_maxVal _ _
    have hmin : minVal (retainedResidual cornerQ2 Wr competitor2) = (0 : ℝ) / 17 := by
      refine le_antisymm ?_ (le_minVal _ ?_)
      · rw [← retained_com_min_val]
        exact minVal_le _ _
      · intro z
        rw [Wr_retained_competitor, ← retained_com_min_val, Wr_retained_competitor]
        exact div17_le (residual_competitor_bounds z).1
    unfold osc; rw [hmax, hmin]; ring
  unfold productCompressionLoss
  rw [show (fun x ↦ Wr x - selected2.sum (fun j ↦ productResponse cornerQ2 Wr j (x j))) =
      retainedResidual cornerQ2 Wr selected2 from rfl,
    show (fun x ↦ Wr x - competitor2.sum (fun j ↦ productResponse cornerQ2 Wr j (x j))) =
      retainedResidual cornerQ2 Wr competitor2 from rfl, hS, hT]
  ring

theorem witness2_violates_five :
    (5 : ℝ) < 2 * (productCompressionLoss Wr (productResponse cornerQ2 Wr) selected2 -
      productCompressionLoss Wr (productResponse cornerQ2 Wr) competitor2) := by
  rw [witness2_doubled_gap]; norm_num

/-- The `(m-1)` decision bound is FALSE on this cell, with no rank hypothesis. -/
theorem binary_decisionInteraction_constant_five_false :
    ¬ DecisionInteractionConstantAtMost witnessCell2 5 := by
  intro h
  have hbad := h Wr witness2_cell_valid Wr_unitInteraction
  show False
  have : 2 * (productCompressionLoss Wr (productResponse cornerQ2 Wr) selected2 -
      productCompressionLoss Wr (productResponse cornerQ2 Wr) competitor2) ≤ 5 := hbad
  linarith [witness2_violates_five]

theorem binary_witness_summary :
    witnessCell2.BalancedComplement ∧
    witnessCell2.Valid Wr ∧
    UnitInteractionBound Wr ∧
    StrictTopC witnessCell2 Wr ∧
    (5 : ℝ) < 2 * (productCompressionLoss Wr (productResponse cornerQ2 Wr) selected2 -
      productCompressionLoss Wr (productResponse cornerQ2 Wr) competitor2) :=
  ⟨witness2_balanced, witness2_cell_valid, Wr_unitInteraction,
   witness2_strictTopC, witness2_violates_five⟩

/-! ## Corollary: the raw rank-one rescue dies at no extra cost

At `|U| = 2` the raw local contrast is rank one for EVERY world
(`binary_allCoordinatesRawLocalContrastRankOne`, already proved), so the witness
satisfies the raw hypothesis for free.  The raw invariant therefore does not
rescue the `(m-1)` law -- and never could have, because the bound already fails
where the invariant carries no information at all. -/

theorem Wr_allCoordinatesRawRankOne : AllCoordinatesRawLocalContrastRankOne Wr :=
  binary_allCoordinatesRawLocalContrastRankOne Wr

theorem raw_rankOne_does_not_rescue_m_minus_one :
    AllCoordinatesRawLocalContrastRankOne Wr ∧
    witnessCell2.Valid Wr ∧
    UnitInteractionBound Wr ∧
    StrictTopC witnessCell2 Wr ∧
    (5 : ℝ) < 2 * (productCompressionLoss Wr (productResponse cornerQ2 Wr) selected2 -
      productCompressionLoss Wr (productResponse cornerQ2 Wr) competitor2) :=
  ⟨Wr_allCoordinatesRawRankOne, witness2_cell_valid, Wr_unitInteraction,
   witness2_strictTopC, witness2_violates_five⟩

end CIGAMF.P13.D6BinaryBridgeV1
