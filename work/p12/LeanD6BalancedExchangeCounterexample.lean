import Mathlib
import «LeanD6HalfFactorCore»
import «LeanFunctionalRankingV6»

/-!
# Exact counterexample to the proposed balanced one-swap BEX lemma

This does **not** refute H3 or the D6 half-factor conjecture.  It refutes the
proposed intermediate claim that, in the balanced-complement case, at least
one first Top-C exchange must cost at most `delta / 2` in transfer error.

The witness has four binary coordinates, budget two, a normalized product
point-mass reference, integer world values, and `deltaSquare = 17`.  The Top-C
set is `{0,1}`.  Every one-swap neighbour has transfer-error decrement
strictly larger than `17/2`; the smallest is `21/2`.
-/

namespace CIGAMF.P13.D6BalancedExchangeCounterexample

open scoped BigOperators Matrix
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6HalfFactorCore
open CIGAMF.V6.FunctionalRanking

def anchor4 : Fin 4 → Fin 2 := ![1, 1, 0, 1]

def pointMassAnchor4 (i : Fin 4) (u : Fin 2) : ℝ :=
  if u = anchor4 i then 1 else 0

/- Lexicographic values `0000, ..., 1111`:
   `[1,3,-1,-4,-1,-3,-2,-1,-1,-2,-2,-1,7,9,-3,9]`. -/
def bexWorld4 (x : Fin 4 → Fin 2) : ℝ :=
  if x 0 = 0 then
    if x 1 = 0 then
      if x 2 = 0 then (if x 3 = 0 then 1 else 3)
      else (if x 3 = 0 then -1 else -4)
    else
      if x 2 = 0 then (if x 3 = 0 then -1 else -3)
      else (if x 3 = 0 then -2 else -1)
  else
    if x 1 = 0 then
      if x 2 = 0 then (if x 3 = 0 then -1 else -2)
      else (if x 3 = 0 then -2 else -1)
    else
      if x 2 = 0 then (if x 3 = 0 then 7 else 9)
      else (if x 3 = 0 then -3 else 9)

def action4 (a b c d : Fin 2) : Fin 4 → Fin 2 := ![a,b,c,d]

private theorem fin2_zero_or_one (u : Fin 2) : u = 0 ∨ u = 1 := by
  fin_cases u <;> simp

theorem pointMassAnchor4_jointWeight (c : Fin 4 → Fin 2) :
    jointWeight pointMassAnchor4 c = if c = anchor4 then 1 else 0 := by
  classical
  by_cases h : c = anchor4
  · subst c
    norm_num [jointWeight, pointMassAnchor4, anchor4, Fin.prod_univ_four]
  · have hc : c 0 ≠ anchor4 0 ∨ c 1 ≠ anchor4 1 ∨
        c 2 ≠ anchor4 2 ∨ c 3 ≠ anchor4 3 := by
      by_contra hn
      push_neg at hn
      apply h
      funext i
      fin_cases i <;> simp [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2]
    rcases hc with hc | hc | hc | hc <;>
      simp [jointWeight, pointMassAnchor4, Fin.prod_univ_four, hc, h]

theorem pointMassAnchor4_expectation (G : (Fin 4 → Fin 2) → ℝ) :
    productExpectation pointMassAnchor4 G = G anchor4 := by
  classical
  unfold productExpectation
  simp_rw [pointMassAnchor4_jointWeight]
  rw [Finset.sum_eq_single anchor4]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

@[simp] theorem bex_response_zero (j : Fin 4) :
    productResponse pointMassAnchor4 bexWorld4 j 0 =
      ![(-3 : ℝ), -2, 9, 7] j := by
  unfold productResponse
  rw [pointMassAnchor4_expectation]
  fin_cases j <;> simp [bexWorld4, anchor4, Function.update]

@[simp] theorem bex_response_one (j : Fin 4) :
    productResponse pointMassAnchor4 bexWorld4 j 1 =
      ![(9 : ℝ), 9, 9, 9] j := by
  unfold productResponse
  rw [pointMassAnchor4_expectation]
  fin_cases j <;> simp [bexWorld4, anchor4, Function.update]

theorem bex_response_span (j : Fin 4) :
    osc (productResponse pointMassAnchor4 bexWorld4 j) =
      ![(12 : ℝ), 11, 0, 2] j := by
  rw [osc, maxVal_fin2, minVal_fin2]
  fin_cases j <;> norm_num

def selected : Finset (Fin 4) := {0,1}
def swap02 : Finset (Fin 4) := {1,2}
def swap03 : Finset (Fin 4) := {1,3}
def swap12 : Finset (Fin 4) := {0,2}
def swap13 : Finset (Fin 4) := {0,3}

theorem selected_is_topC :
    IsTopKByScore
      (fun j ↦ osc (productResponse pointMassAnchor4 bexWorld4 j))
      selected 2 := by
  constructor
  · simp [selected]
  · intro candidate hcard
    simp_rw [bex_response_span]
    fin_cases candidate <;> simp_all [selected] <;> norm_num at * <;> omega

private theorem compressionLoss_eq_of_bounds
    (S : Finset (Fin 4)) (lo hi : ℝ)
    (hbound : ∀ x, lo ≤ bexWorld4 x -
        S.sum (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (x j)) ∧
      bexWorld4 x -
        S.sum (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (x j)) ≤ hi)
    (xmin xmax : Fin 4 → Fin 2)
    (hmin : bexWorld4 xmin -
        S.sum (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (xmin j)) = lo)
    (hmax : bexWorld4 xmax -
        S.sum (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (xmax j)) = hi) :
    productCompressionLoss bexWorld4
      (productResponse pointMassAnchor4 bexWorld4) S = (hi - lo) / 2 := by
  let r : (Fin 4 → Fin 2) → ℝ := fun x ↦ bexWorld4 x -
    S.sum (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (x j))
  have hrmax : maxVal r = hi := by
    apply le_antisymm
    · exact maxVal_le r (fun x ↦ (hbound x).2)
    · simpa [r, hmax] using le_maxVal r xmax
  have hrmin : minVal r = lo := by
    apply le_antisymm
    · simpa [r, hmin] using minVal_le r xmin
    · exact le_minVal r (fun x ↦ (hbound x).1)
  simp [productCompressionLoss, r, osc, hrmax, hrmin]

private theorem selected_bounds (x : Fin 4 → Fin 2) :
    -21 ≤ bexWorld4 x - selected.sum
      (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (x j)) ∧
    bexWorld4 x - selected.sum
      (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (x j)) ≤ 8 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [selected, bexWorld4, h0, h1, h2, h3] <;> norm_num

private theorem swap02_bounds (x : Fin 4 → Fin 2) :
    -21 ≤ bexWorld4 x - swap02.sum
      (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (x j)) ∧
    bexWorld4 x - swap02.sum
      (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (x j)) ≤ -4 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [swap02, bexWorld4, h0, h1, h2, h3] <;> norm_num

private theorem swap03_bounds (x : Fin 4 → Fin 2) :
    -21 ≤ bexWorld4 x - swap03.sum
      (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (x j)) ∧
    bexWorld4 x - swap03.sum
      (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (x j)) ≤ -4 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [swap03, bexWorld4, h0, h1, h2, h3] <;> norm_num

private theorem swap12_bounds (x : Fin 4 → Fin 2) :
    -21 ≤ bexWorld4 x - swap12.sum
      (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (x j)) ∧
    bexWorld4 x - swap12.sum
      (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (x j)) ≤ -3 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [swap12, bexWorld4, h0, h1, h2, h3] <;> norm_num

private theorem swap13_bounds (x : Fin 4 → Fin 2) :
    -20 ≤ bexWorld4 x - swap13.sum
      (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (x j)) ∧
    bexWorld4 x - swap13.sum
      (fun j ↦ productResponse pointMassAnchor4 bexWorld4 j (x j)) ≤ -3 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [swap13, bexWorld4, h0, h1, h2, h3] <;> norm_num

theorem selected_true_loss :
    productCompressionLoss bexWorld4
      (productResponse pointMassAnchor4 bexWorld4) selected = 29 / 2 := by
  convert compressionLoss_eq_of_bounds selected (-21) 8 selected_bounds
    (action4 1 1 1 0) (action4 0 0 0 1) (by
      simp [selected, action4, bexWorld4] <;> norm_num) (by
      simp [selected, action4, bexWorld4] <;> norm_num) using 1 <;> norm_num

theorem swap02_true_loss :
    productCompressionLoss bexWorld4
      (productResponse pointMassAnchor4 bexWorld4) swap02 = 17 / 2 := by
  convert compressionLoss_eq_of_bounds swap02 (-21) (-4) swap02_bounds
    (action4 0 1 0 1) (action4 0 0 0 1) (by
      simp [swap02, action4, bexWorld4] <;> norm_num) (by
      simp [swap02, action4, bexWorld4] <;> norm_num) using 1 <;> norm_num

theorem swap03_true_loss :
    productCompressionLoss bexWorld4
      (productResponse pointMassAnchor4 bexWorld4) swap03 = 17 / 2 := by
  convert compressionLoss_eq_of_bounds swap03 (-21) (-4) swap03_bounds
    (action4 0 1 0 1) (action4 0 0 0 0) (by
      simp [swap03, action4, bexWorld4] <;> norm_num) (by
      simp [swap03, action4, bexWorld4] <;> norm_num) using 1 <;> norm_num

theorem swap12_true_loss :
    productCompressionLoss bexWorld4
      (productResponse pointMassAnchor4 bexWorld4) swap12 = 9 := by
  convert compressionLoss_eq_of_bounds swap12 (-21) (-3) swap12_bounds
    (action4 1 1 1 0) (action4 0 0 0 1) (by
      simp [swap12, action4, bexWorld4] <;> norm_num) (by
      simp [swap12, action4, bexWorld4] <;> norm_num) using 1 <;> norm_num

theorem swap13_true_loss :
    productCompressionLoss bexWorld4
      (productResponse pointMassAnchor4 bexWorld4) swap13 = 17 / 2 := by
  convert compressionLoss_eq_of_bounds swap13 (-20) (-3) swap13_bounds
    (action4 1 0 0 1) (action4 0 0 0 0) (by
      simp [swap13, action4, bexWorld4] <;> norm_num) (by
      simp [swap13, action4, bexWorld4] <;> norm_num) using 1 <;> norm_num

private theorem surrogate_loss (S : Finset (Fin 4)) :
    productCompressionLoss (productA pointMassAnchor4 bexWorld4)
      (productResponse pointMassAnchor4 bexWorld4) S =
      Sᶜ.sum (fun j ↦ ![(12 : ℝ), 11, 0, 2] j) / 2 := by
  rw [productA_compression_loss_formula]
  apply congrArg (fun z : ℝ ↦ z / 2)
  apply Finset.sum_congr rfl
  intro j hj
  exact bex_response_span j

theorem selected_transfer :
    transferErr pointMassAnchor4 bexWorld4 selected = 27 / 2 := by
  rw [transferErr, selected_true_loss, surrogate_loss]
  have hc : selectedᶜ = ({2,3} : Finset (Fin 4)) := by
    ext j
    fin_cases j <;> simp [selected]
  rw [hc]
  simp
  norm_num

theorem swap02_transfer :
    transferErr pointMassAnchor4 bexWorld4 swap02 = 3 / 2 := by
  rw [transferErr, swap02_true_loss, surrogate_loss]
  have hc : swap02ᶜ = ({0,3} : Finset (Fin 4)) := by
    ext j
    fin_cases j <;> simp [swap02]
  rw [hc]
  simp
  norm_num

theorem swap03_transfer :
    transferErr pointMassAnchor4 bexWorld4 swap03 = 5 / 2 := by
  rw [transferErr, swap03_true_loss, surrogate_loss]
  have hc : swap03ᶜ = ({0,2} : Finset (Fin 4)) := by
    ext j
    fin_cases j <;> simp [swap03]
  rw [hc]
  simp
  norm_num

theorem swap12_transfer :
    transferErr pointMassAnchor4 bexWorld4 swap12 = 5 / 2 := by
  rw [transferErr, swap12_true_loss, surrogate_loss]
  have hc : swap12ᶜ = ({1,3} : Finset (Fin 4)) := by
    ext j
    fin_cases j <;> simp [swap12]
  rw [hc]
  simp
  norm_num

theorem swap13_transfer :
    transferErr pointMassAnchor4 bexWorld4 swap13 = 3 := by
  rw [transferErr, swap13_true_loss, surrogate_loss]
  have hc : swap13ᶜ = ({1,2} : Finset (Fin 4)) := by
    ext j
    fin_cases j <;> simp [swap13]
  rw [hc]
  simp
  norm_num

theorem BEX_balanced_existential_route_counterexample :
    IsTopKByScore
      (fun j ↦ osc (productResponse pointMassAnchor4 bexWorld4 j))
      selected 2 ∧
    selected.card = 2 ∧ selectedᶜ.card = 2 ∧
    (∀ U ∈ ({swap02, swap03, swap12, swap13} : Finset (Finset (Fin 4))),
      transferErr pointMassAnchor4 bexWorld4 selected -
        transferErr pointMassAnchor4 bexWorld4 U > (17 : ℝ) / 2) := by
  have hc : selectedᶜ = ({2,3} : Finset (Fin 4)) := by
    ext j
    fin_cases j <;> simp [selected]
  refine ⟨selected_is_topC, by simp [selected], by rw [hc]; simp, ?_⟩
  intro U hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with rfl | rfl | rfl | rfl
  · rw [selected_transfer, swap02_transfer]
    norm_num
  · rw [selected_transfer, swap03_transfer]
    norm_num
  · rw [selected_transfer, swap12_transfer]
    norm_num
  · rw [selected_transfer, swap13_transfer]
    norm_num

end CIGAMF.P13.D6BalancedExchangeCounterexample
