import Mathlib
import «LeanD6BinaryIntegerCounterexampleV1»
import «LeanD6ContrastRankPhaseDefinitionsV2»
import «LeanD6PolyhedralActiveCellV1»
import «LeanD6RawLocalContrastRankOneV1»

/-!
# Bridge PART A (integer identifications only): the binary counterexample, in the chain's own vocabulary

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


end CIGAMF.P13.D6BinaryBridgeV1
