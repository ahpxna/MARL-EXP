import Mathlib
import «LeanD6HalfFactorCore»
import «LeanFunctionalRankingV6»

/-!
# Exact counterexample to DBEX and BEX-with-score-credit

This module checks the new local routes mentioned in the V2 worker brief.  It
does not refute the D6 half-factor headline: it refutes only the proposed
claim that one first Top-C swap must be cheap either in true loss (`DBEX`) or
after paying transfer error with the swapped response-score gap.
-/

namespace CIGAMF.P13.D6DBEXCreditCounterexample

open scoped BigOperators Matrix
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6HalfFactorCore
open CIGAMF.V6.FunctionalRanking

def anchor4 : Fin 4 → Fin 2 := ![1,0,1,1]

def pointMassAnchor4 (i : Fin 4) (u : Fin 2) : ℝ :=
  if u = anchor4 i then 1 else 0

/- Lexicographic values `0000, ..., 1111`. -/
def dbexWorld4 (x : Fin 4 → Fin 2) : ℝ :=
  if x 0 = 0 then
    if x 1 = 0 then
      if x 2 = 0 then (if x 3 = 0 then -8 else -20)
      else (if x 3 = 0 then 35 else 31)
    else
      if x 2 = 0 then (if x 3 = 0 then -13 else -21)
      else (if x 3 = 0 then 8 else 6)
  else
    if x 1 = 0 then
      if x 2 = 0 then (if x 3 = 0 then -8 else -14)
      else (if x 3 = 0 then 15 else 7)
    else
      if x 2 = 0 then (if x 3 = 0 then -8 else -40)
      else (if x 3 = 0 then 14 else -18)

def action4 (a b c d : Fin 2) : Fin 4 → Fin 2 := ![a,b,c,d]

private theorem fin2_zero_or_one (u : Fin 2) : u = 0 ∨ u = 1 := by
  fin_cases u <;> simp

theorem pointMass_jointWeight (c : Fin 4 → Fin 2) :
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

theorem pointMass_expectation (G : (Fin 4 → Fin 2) → ℝ) :
    productExpectation pointMassAnchor4 G = G anchor4 := by
  classical
  unfold productExpectation
  simp_rw [pointMass_jointWeight]
  rw [Finset.sum_eq_single anchor4]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

@[simp] theorem response_zero (j : Fin 4) :
    productResponse pointMassAnchor4 dbexWorld4 j 0 =
      ![(31 : ℝ), 7, -14, 15] j := by
  unfold productResponse
  rw [pointMass_expectation]
  fin_cases j <;> simp [dbexWorld4, anchor4, Function.update]

@[simp] theorem response_one (j : Fin 4) :
    productResponse pointMassAnchor4 dbexWorld4 j 1 =
      ![(7 : ℝ), -18, 7, 7] j := by
  unfold productResponse
  rw [pointMass_expectation]
  fin_cases j <;> simp [dbexWorld4, anchor4, Function.update]

theorem response_span (j : Fin 4) :
    osc (productResponse pointMassAnchor4 dbexWorld4 j) =
      ![(24 : ℝ), 25, 21, 8] j := by
  rw [osc, maxVal_fin2, minVal_fin2]
  fin_cases j <;> norm_num

def selected : Finset (Fin 4) := {0,1}
def competitor : Finset (Fin 4) := {2,3}
def swap02 : Finset (Fin 4) := {1,2}
def swap03 : Finset (Fin 4) := {1,3}
def swap12 : Finset (Fin 4) := {0,2}
def swap13 : Finset (Fin 4) := {0,3}

theorem selected_is_topC :
    IsTopKByScore
      (fun j ↦ osc (productResponse pointMassAnchor4 dbexWorld4 j))
      selected 2 := by
  constructor
  · simp [selected]
  · intro candidate hcard
    simp_rw [response_span]
    fin_cases candidate <;> simp_all [selected] <;> norm_num at * <;> omega

private theorem compressionLoss_eq_of_bounds
    (S : Finset (Fin 4)) (lo hi : ℝ)
    (hbound : ∀ x, lo ≤ dbexWorld4 x -
        S.sum (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (x j)) ∧
      dbexWorld4 x -
        S.sum (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (x j)) ≤ hi)
    (xmin xmax : Fin 4 → Fin 2)
    (hmin : dbexWorld4 xmin -
        S.sum (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (xmin j)) = lo)
    (hmax : dbexWorld4 xmax -
        S.sum (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (xmax j)) = hi) :
    productCompressionLoss dbexWorld4
      (productResponse pointMassAnchor4 dbexWorld4) S = (hi - lo) / 2 := by
  let r : (Fin 4 → Fin 2) → ℝ := fun x ↦ dbexWorld4 x -
    S.sum (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (x j))
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
    -58 ≤ dbexWorld4 x - selected.sum
      (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (x j)) ∧
    dbexWorld4 x - selected.sum
      (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (x j)) ≤ 25 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [selected, dbexWorld4, h0, h1, h2, h3] <;> norm_num

private theorem swap02_bounds (x : Fin 4 → Fin 2) :
    -13 ≤ dbexWorld4 x - swap02.sum
      (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (x j)) ∧
    dbexWorld4 x - swap02.sum
      (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (x j)) ≤ 25 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [swap02, dbexWorld4, h0, h1, h2, h3] <;> norm_num

private theorem swap03_bounds (x : Fin 4 → Fin 2) :
    -34 ≤ dbexWorld4 x - swap03.sum
      (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (x j)) ∧
    dbexWorld4 x - swap03.sum
      (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (x j)) ≤ 17 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [swap03, dbexWorld4, h0, h1, h2, h3] <;> norm_num

private theorem swap12_bounds (x : Fin 4 → Fin 2) :
    -38 ≤ dbexWorld4 x - swap12.sum
      (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (x j)) ∧
    dbexWorld4 x - swap12.sum
      (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (x j)) ≤ 1 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [swap12, dbexWorld4, h0, h1, h2, h3] <;> norm_num

private theorem swap13_bounds (x : Fin 4 → Fin 2) :
    -59 ≤ dbexWorld4 x - swap13.sum
      (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (x j)) ∧
    dbexWorld4 x - swap13.sum
      (fun j ↦ productResponse pointMassAnchor4 dbexWorld4 j (x j)) ≤ -7 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [swap13, dbexWorld4, h0, h1, h2, h3] <;> norm_num

theorem selected_true_loss :
    productCompressionLoss dbexWorld4
      (productResponse pointMassAnchor4 dbexWorld4) selected = 83 / 2 := by
  convert compressionLoss_eq_of_bounds selected (-58) 25 selected_bounds
    (action4 0 0 0 1) (action4 1 1 1 0) (by
      simp [selected, action4, dbexWorld4] <;> norm_num) (by
      simp [selected, action4, dbexWorld4] <;> norm_num) using 1 <;> norm_num

theorem swap02_true_loss :
    productCompressionLoss dbexWorld4
      (productResponse pointMassAnchor4 dbexWorld4) swap02 = 19 := by
  convert compressionLoss_eq_of_bounds swap02 (-13) 25 swap02_bounds
    (action4 0 0 0 1) (action4 1 1 1 0) (by
      simp [swap02, action4, dbexWorld4] <;> norm_num) (by
      simp [swap02, action4, dbexWorld4] <;> norm_num) using 1 <;> norm_num

theorem swap03_true_loss :
    productCompressionLoss dbexWorld4
      (productResponse pointMassAnchor4 dbexWorld4) swap03 = 51 / 2 := by
  convert compressionLoss_eq_of_bounds swap03 (-34) 17 swap03_bounds
    (action4 0 0 0 1) (action4 1 1 1 0) (by
      simp [swap03, action4, dbexWorld4] <;> norm_num) (by
      simp [swap03, action4, dbexWorld4] <;> norm_num) using 1 <;> norm_num

theorem swap12_true_loss :
    productCompressionLoss dbexWorld4
      (productResponse pointMassAnchor4 dbexWorld4) swap12 = 39 / 2 := by
  convert compressionLoss_eq_of_bounds swap12 (-38) 1 swap12_bounds
    (action4 0 1 0 1) (action4 1 0 1 0) (by
      simp [swap12, action4, dbexWorld4] <;> norm_num) (by
      simp [swap12, action4, dbexWorld4] <;> norm_num) using 1 <;> norm_num

theorem swap13_true_loss :
    productCompressionLoss dbexWorld4
      (productResponse pointMassAnchor4 dbexWorld4) swap13 = 26 := by
  convert compressionLoss_eq_of_bounds swap13 (-59) (-7) swap13_bounds
    (action4 0 1 0 0) (action4 1 0 1 1) (by
      simp [swap13, action4, dbexWorld4] <;> norm_num) (by
      simp [swap13, action4, dbexWorld4] <;> norm_num) using 1 <;> norm_num

private theorem surrogate_loss (S : Finset (Fin 4)) :
    productCompressionLoss (productA pointMassAnchor4 dbexWorld4)
      (productResponse pointMassAnchor4 dbexWorld4) S =
      Sᶜ.sum (fun j ↦ ![(24 : ℝ), 25, 21, 8] j) / 2 := by
  rw [productA_compression_loss_formula]
  apply congrArg (fun z : ℝ ↦ z / 2)
  apply Finset.sum_congr rfl
  intro j hj
  exact response_span j

theorem selected_transfer :
    transferErr pointMassAnchor4 dbexWorld4 selected = 27 := by
  rw [transferErr, selected_true_loss, surrogate_loss]
  have hc : selectedᶜ = ({2,3} : Finset (Fin 4)) := by
    ext j; fin_cases j <;> simp [selected]
  rw [hc]
  simp
  norm_num

theorem swaps_transfer_three
    (U : Finset (Fin 4))
    (hU : U ∈ ({swap02, swap03, swap12, swap13} : Finset (Finset (Fin 4)))) :
    transferErr pointMassAnchor4 dbexWorld4 U = 3 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with rfl | rfl | rfl | rfl
  all_goals rw [transferErr, surrogate_loss]
  · rw [swap02_true_loss]
    have hc : swap02ᶜ = ({0,3} : Finset (Fin 4)) := by
      ext j; fin_cases j <;> simp [swap02]
    rw [hc]; simp; norm_num
  · rw [swap03_true_loss]
    have hc : swap03ᶜ = ({0,2} : Finset (Fin 4)) := by
      ext j; fin_cases j <;> simp [swap03]
    rw [hc]; simp; norm_num
  · rw [swap12_true_loss]
    have hc : swap12ᶜ = ({1,3} : Finset (Fin 4)) := by
      ext j; fin_cases j <;> simp [swap12]
    rw [hc]; simp; norm_num
  · rw [swap13_true_loss]
    have hc : swap13ᶜ = ({1,2} : Finset (Fin 4)) := by
      ext j; fin_cases j <;> simp [swap13]
    rw [hc]; simp; norm_num

theorem DBEX_all_first_swaps_fail :
    ∀ U ∈ ({swap02, swap03, swap12, swap13} : Finset (Finset (Fin 4))),
      productCompressionLoss dbexWorld4
          (productResponse pointMassAnchor4 dbexWorld4) selected -
        productCompressionLoss dbexWorld4
          (productResponse pointMassAnchor4 dbexWorld4) U > (30 : ℝ) / 2 := by
  intro U hU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with rfl | rfl | rfl | rfl
  · rw [selected_true_loss, swap02_true_loss]; norm_num
  · rw [selected_true_loss, swap03_true_loss]; norm_num
  · rw [selected_true_loss, swap12_true_loss]; norm_num
  · rw [selected_true_loss, swap13_true_loss]; norm_num

/- Each ordered Top-C swap also violates
`E(S)-E(S-i+j) ≤ (delta + C_i-C_j)/2`. -/
theorem BEX_credit_all_first_swaps_fail :
    transferErr pointMassAnchor4 dbexWorld4 selected -
        transferErr pointMassAnchor4 dbexWorld4 swap02 > (30 + 24 - 21 : ℝ) / 2 ∧
    transferErr pointMassAnchor4 dbexWorld4 selected -
        transferErr pointMassAnchor4 dbexWorld4 swap03 > (30 + 24 - 8 : ℝ) / 2 ∧
    transferErr pointMassAnchor4 dbexWorld4 selected -
        transferErr pointMassAnchor4 dbexWorld4 swap12 > (30 + 25 - 21 : ℝ) / 2 ∧
    transferErr pointMassAnchor4 dbexWorld4 selected -
        transferErr pointMassAnchor4 dbexWorld4 swap13 > (30 + 25 - 8 : ℝ) / 2 := by
  have h02 : transferErr pointMassAnchor4 dbexWorld4 swap02 = 3 :=
    swaps_transfer_three swap02 (by simp)
  have h03 : transferErr pointMassAnchor4 dbexWorld4 swap03 = 3 :=
    swaps_transfer_three swap03 (by simp)
  have h12 : transferErr pointMassAnchor4 dbexWorld4 swap12 = 3 :=
    swaps_transfer_three swap12 (by simp)
  have h13 : transferErr pointMassAnchor4 dbexWorld4 swap13 = 3 :=
    swaps_transfer_three swap13 (by simp)
  rw [selected_transfer, h02, h03, h12, h13]
  norm_num

end CIGAMF.P13.D6DBEXCreditCounterexample
