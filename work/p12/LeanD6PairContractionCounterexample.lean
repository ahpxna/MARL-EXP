import Mathlib
import «LeanProductMixedDifferenceV4»
import «LeanFunctionalRankingV6»

/-!
# Exact counterexample to pair-contraction induction

The four reduced worlds below are the literal point-mass contractions of one
selected and one rejected coordinate.  All four violate the proposed
`D_F ≤ delta + D_bar` step.  This kills only pair-contraction induction;
the witness remains inside the D6 half-factor headline.
-/

namespace CIGAMF.P13.D6PairContractionCounterexample

open scoped BigOperators Matrix
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.V6.FunctionalRanking

def anchor4 : Fin 4 → Fin 2 := ![0,0,0,1]

def pointMass4 (i : Fin 4) (u : Fin 2) : ℝ :=
  if u = anchor4 i then 1 else 0

@[simp] def pcWorld4Z (x : Fin 4 → Fin 2) : ℤ :=
  if x 0 = 0 then
    if x 1 = 0 then
      if x 2 = 0 then (if x 3 = 0 then -3 else -11)
      else (if x 3 = 0 then -8 else -3)
    else
      if x 2 = 0 then (if x 3 = 0 then -1 else -4)
      else (if x 3 = 0 then 0 else 1)
  else
    if x 1 = 0 then
      if x 2 = 0 then (if x 3 = 0 then -2 else -5)
      else (if x 3 = 0 then 2 else 1)
    else
      if x 2 = 0 then (if x 3 = 0 then 9 else 10)
      else (if x 3 = 0 then 5 else 6)

def pcWorld4 (x : Fin 4 → Fin 2) : ℝ := pcWorld4Z x

def action4 (a b c d : Fin 2) : Fin 4 → Fin 2 := ![a,b,c,d]

private theorem fin2_zero_or_one (u : Fin 2) : u = 0 ∨ u = 1 := by
  fin_cases u <;> simp

theorem pointMass4_expectation (G : (Fin 4 → Fin 2) → ℝ) :
    productExpectation pointMass4 G = G anchor4 := by
  classical
  have hweight (c : Fin 4 → Fin 2) :
      jointWeight pointMass4 c = if c = anchor4 then 1 else 0 := by
    by_cases h : c = anchor4
    · subst c
      norm_num [jointWeight, pointMass4, anchor4, Fin.prod_univ_four]
    · have hc : c 0 ≠ anchor4 0 ∨ c 1 ≠ anchor4 1 ∨
          c 2 ≠ anchor4 2 ∨ c 3 ≠ anchor4 3 := by
        by_contra hn
        push_neg at hn
        apply h
        funext i
        fin_cases i <;> simp [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2]
      rcases hc with hc | hc | hc | hc <;>
        simp [jointWeight, pointMass4, Fin.prod_univ_four, hc, h]
  unfold productExpectation
  simp_rw [hweight]
  rw [Finset.sum_eq_single anchor4]
  · simp
  · intro c hc hne
    simp [hne]
  · simp

@[simp] theorem response_zero (j : Fin 4) :
    productResponse pointMass4 pcWorld4 j 0 =
      ![(-11 : ℝ), -11, -11, -3] j := by
  unfold productResponse
  rw [pointMass4_expectation]
  fin_cases j <;> simp [pcWorld4, anchor4, Function.update]

@[simp] theorem response_one (j : Fin 4) :
    productResponse pointMass4 pcWorld4 j 1 =
      ![(-5 : ℝ), -4, -3, -11] j := by
  unfold productResponse
  rw [pointMass4_expectation]
  fin_cases j <;> simp [pcWorld4, anchor4, Function.update]

theorem response_span (j : Fin 4) :
    osc (productResponse pointMass4 pcWorld4 j) =
      ![(6 : ℝ), 7, 8, 8] j := by
  rw [osc, maxVal_fin2, minVal_fin2]
  fin_cases j <;> norm_num

def selected : Finset (Fin 4) := {2,3}
def competitor : Finset (Fin 4) := {0,1}

theorem selected_is_topC :
    IsTopKByScore (fun j ↦ osc (productResponse pointMass4 pcWorld4 j))
      selected 2 := by
  constructor
  · simp [selected]
  · intro candidate hcard
    simp_rw [response_span]
    fin_cases candidate <;> simp_all [selected] <;> norm_num at * <;> omega

private theorem compressionLoss_eq_of_bounds
    {r : Type*} [Fintype r] [Nonempty r]
    (F : r → ℝ) (Q : Finset (Fin 4) → r → ℝ)
    (S : Finset (Fin 4)) (lo hi : ℝ)
    (hbound : ∀ x, lo ≤ F x - Q S x ∧ F x - Q S x ≤ hi)
    (xmin xmax : r) (hmin : F xmin - Q S xmin = lo)
    (hmax : F xmax - Q S xmax = hi)
    (hLoss : productCompressionLoss pcWorld4
      (productResponse pointMass4 pcWorld4) S =
      osc (fun x ↦ F x - Q S x) / 2) :
    productCompressionLoss pcWorld4
      (productResponse pointMass4 pcWorld4) S = (hi - lo) / 2 := by
  have hrmax : maxVal (fun x ↦ F x - Q S x) = hi := by
    apply le_antisymm
    · exact maxVal_le _ (fun x ↦ (hbound x).2)
    · simpa [hmax] using le_maxVal (fun x ↦ F x - Q S x) xmax
  have hrmin : minVal (fun x ↦ F x - Q S x) = lo := by
    apply le_antisymm
    · simpa [hmin] using minVal_le (fun x ↦ F x - Q S x) xmin
    · exact le_minVal _ (fun x ↦ (hbound x).1)
  rw [hLoss, osc, hrmax, hrmin]

private theorem selected_bounds (x : Fin 4 → Fin 2) :
    -2 ≤ pcWorld4 x - selected.sum
      (fun j ↦ productResponse pointMass4 pcWorld4 j (x j)) ∧
    pcWorld4 x - selected.sum
      (fun j ↦ productResponse pointMass4 pcWorld4 j (x j)) ≤ 32 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [selected, pcWorld4, h0, h1, h2, h3] <;> norm_num

private theorem competitor_bounds (x : Fin 4 → Fin 2) :
    11 ≤ pcWorld4 x - competitor.sum
      (fun j ↦ productResponse pointMass4 pcWorld4 j (x j)) ∧
    pcWorld4 x - competitor.sum
      (fun j ↦ productResponse pointMass4 pcWorld4 j (x j)) ≤ 19 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [competitor, pcWorld4, h0, h1, h2, h3] <;> norm_num

theorem selected_loss :
    productCompressionLoss pcWorld4 (productResponse pointMass4 pcWorld4)
      selected = 17 := by
  let Q : Finset (Fin 4) → (Fin 4 → Fin 2) → ℝ := fun S x ↦
    S.sum (fun j ↦ productResponse pointMass4 pcWorld4 j (x j))
  have h := compressionLoss_eq_of_bounds pcWorld4 Q selected (-2) 32
    selected_bounds (action4 0 0 1 0) (action4 1 1 0 1)
    (by simp [Q, selected, action4, pcWorld4] <;> norm_num)
    (by simp [Q, selected, action4, pcWorld4] <;> norm_num)
    (by rfl)
  norm_num at h
  exact h

theorem competitor_loss :
    productCompressionLoss pcWorld4 (productResponse pointMass4 pcWorld4)
      competitor = 4 := by
  let Q : Finset (Fin 4) → (Fin 4 → Fin 2) → ℝ := fun S x ↦
    S.sum (fun j ↦ productResponse pointMass4 pcWorld4 j (x j))
  have h := compressionLoss_eq_of_bounds pcWorld4 Q competitor 11 19
    competitor_bounds (action4 0 0 0 1) (action4 1 1 0 1)
    (by simp [Q, competitor, action4, pcWorld4] <;> norm_num)
    (by simp [Q, competitor, action4, pcWorld4] <;> norm_num)
    (by rfl)
  norm_num at h
  exact h

def mixedDifferenceZ (i : Fin 4) (x c : Fin 4 → Fin 2) : ℤ :=
  pcWorld4Z x - pcWorld4Z (Function.update x i (c i)) -
    pcWorld4Z (Function.update c i (x i)) + pcWorld4Z c

private theorem mixedDifferenceZ_le_thirteen :
    ∀ (i : Fin 4) (x c : Fin 4 → Fin 2),
      |mixedDifferenceZ i x c| ≤ 13 := by
  native_decide

private theorem mixedDifference_eq_cast
    (i : Fin 4) (x c : Fin 4 → Fin 2) :
    mixedDifference pcWorld4 i x c = (mixedDifferenceZ i x c : ℝ) := by
  simp [mixedDifference, mixedDifferenceZ, pcWorld4]

theorem mixedDifference_le_thirteen
    (i : Fin 4) (x c : Fin 4 → Fin 2) :
    |mixedDifference pcWorld4 i x c| ≤ 13 := by
  have hz := mixedDifferenceZ_le_thirteen i x c
  rw [mixedDifference_eq_cast]
  exact_mod_cast hz

theorem mixedDifference_attains_thirteen :
    |mixedDifference pcWorld4 0 (action4 0 0 0 0) (action4 1 1 0 1)| = 13 := by
  rw [mixedDifference_eq_cast]
  have hz :
      mixedDifferenceZ 0 (action4 0 0 0 0) (action4 1 1 0 1) = (13 : ℤ) := by
    native_decide
  rw [hz]
  norm_num

/- Point-mass contraction fixes the removed pair at its anchor.  The remaining
coordinates are ordered increasingly in each two-coordinate world. -/
def contracted20 (z : Fin 2 → Fin 2) : ℝ := pcWorld4 ![0,z 0,0,z 1]
def contracted21 (z : Fin 2 → Fin 2) : ℝ := pcWorld4 ![z 0,0,0,z 1]
def contracted30 (z : Fin 2 → Fin 2) : ℝ := pcWorld4 ![0,z 0,z 1,1]
def contracted31 (z : Fin 2 → Fin 2) : ℝ := pcWorld4 ![z 0,0,z 1,1]

def anchor01 : Fin 2 → Fin 2 := ![0,1]
def anchor00 : Fin 2 → Fin 2 := ![0,0]
def pointMass2 (a : Fin 2 → Fin 2) (i u : Fin 2) : ℝ :=
  if u = a i then 1 else 0

theorem pointMass2_expectation (a : Fin 2 → Fin 2)
    (G : (Fin 2 → Fin 2) → ℝ) :
    productExpectation (pointMass2 a) G = G a := by
  classical
  have hweight (c : Fin 2 → Fin 2) :
      jointWeight (pointMass2 a) c = if c = a then 1 else 0 := by
    by_cases h : c = a
    · subst c
      norm_num [jointWeight, pointMass2, Fin.prod_univ_two]
    · have hc : c 0 ≠ a 0 ∨ c 1 ≠ a 1 := by
        by_contra hn
        push_neg at hn
        apply h
        funext i
        fin_cases i <;> simp [hn.1, hn.2]
      rcases hc with hc | hc <;>
        simp [jointWeight, pointMass2, Fin.prod_univ_two, hc, h]
  unfold productExpectation
  simp_rw [hweight]
  rw [Finset.sum_eq_single a]
  · simp
  · intro c hc hne
    simp [hne]
  · simp

private theorem reduced_loss_singleton
    (a : Fin 2 → Fin 2) (W : (Fin 2 → Fin 2) → ℝ)
    (selectedIndex : Fin 2) (lo hi : ℝ)
    (hbound : ∀ z, lo ≤ W z -
        productResponse (pointMass2 a) W selectedIndex (z selectedIndex) ∧
      W z - productResponse (pointMass2 a) W selectedIndex (z selectedIndex) ≤ hi)
    (zmin zmax : Fin 2 → Fin 2)
    (hmin : W zmin -
      productResponse (pointMass2 a) W selectedIndex (zmin selectedIndex) = lo)
    (hmax : W zmax -
      productResponse (pointMass2 a) W selectedIndex (zmax selectedIndex) = hi) :
    productCompressionLoss W (productResponse (pointMass2 a) W)
      {selectedIndex} = (hi - lo) / 2 := by
  let r := fun z ↦ W z -
    productResponse (pointMass2 a) W selectedIndex (z selectedIndex)
  have hrmax : maxVal r = hi := by
    apply le_antisymm
    · exact maxVal_le r (fun z ↦ (hbound z).2)
    · simpa [r, hmax] using le_maxVal r zmax
  have hrmin : minVal r = lo := by
    apply le_antisymm
    · simpa [r, hmin] using minVal_le r zmin
    · exact le_minVal r (fun z ↦ (hbound z).1)
  simp [productCompressionLoss, r, osc, hrmax, hrmin]

theorem contracted20_gap :
    productCompressionLoss contracted20
        (productResponse (pointMass2 anchor01) contracted20) {1} -
      productCompressionLoss contracted20
        (productResponse (pointMass2 anchor01) contracted20) {0} = -1 / 2 := by
  have hb1 : ∀ z, 0 ≤ contracted20 z -
      productResponse (pointMass2 anchor01) contracted20 1 (z 1) ∧
      contracted20 z - productResponse (pointMass2 anchor01) contracted20 1 (z 1) ≤ 7 := by
    intro z
    rcases fin2_zero_or_one (z 0) with h0 | h0 <;>
      rcases fin2_zero_or_one (z 1) with h1 | h1 <;>
      simp [productResponse, pointMass2_expectation, contracted20,
        anchor01, pcWorld4, Function.update, h0, h1] <;> norm_num
  have hb0 : ∀ z, 0 ≤ contracted20 z -
      productResponse (pointMass2 anchor01) contracted20 0 (z 0) ∧
      contracted20 z - productResponse (pointMass2 anchor01) contracted20 0 (z 0) ≤ 8 := by
    intro z
    rcases fin2_zero_or_one (z 0) with h0 | h0 <;>
      rcases fin2_zero_or_one (z 1) with h1 | h1 <;>
      simp [productResponse, pointMass2_expectation, contracted20,
        anchor01, pcWorld4, Function.update, h0, h1] <;> norm_num
  rw [reduced_loss_singleton anchor01 contracted20 1 0 7 hb1 ![0,0] ![1,1]
      (by simp [productResponse, pointMass2_expectation, contracted20,
        anchor01, pcWorld4, Function.update] <;> norm_num)
      (by simp [productResponse, pointMass2_expectation, contracted20,
        anchor01, pcWorld4, Function.update] <;> norm_num)]
  rw [reduced_loss_singleton anchor01 contracted20 0 0 8 hb0 ![0,1] ![0,0]
      (by simp [productResponse, pointMass2_expectation, contracted20,
        anchor01, pcWorld4, Function.update] <;> norm_num)
      (by simp [productResponse, pointMass2_expectation, contracted20,
        anchor01, pcWorld4, Function.update] <;> norm_num)]
  norm_num

theorem contracted21_gap :
    productCompressionLoss contracted21
        (productResponse (pointMass2 anchor01) contracted21) {1} -
      productCompressionLoss contracted21
        (productResponse (pointMass2 anchor01) contracted21) {0} = -1 := by
  have hb1 : ∀ z, 0 ≤ contracted21 z -
      productResponse (pointMass2 anchor01) contracted21 1 (z 1) ∧
      contracted21 z - productResponse (pointMass2 anchor01) contracted21 1 (z 1) ≤ 6 := by
    intro z
    rcases fin2_zero_or_one (z 0) with h0 | h0 <;>
      rcases fin2_zero_or_one (z 1) with h1 | h1 <;>
      simp [productResponse, pointMass2_expectation, contracted21,
        anchor01, pcWorld4, Function.update, h0, h1] <;> norm_num
  have hb0 : ∀ z, 0 ≤ contracted21 z -
      productResponse (pointMass2 anchor01) contracted21 0 (z 0) ∧
      contracted21 z - productResponse (pointMass2 anchor01) contracted21 0 (z 0) ≤ 8 := by
    intro z
    rcases fin2_zero_or_one (z 0) with h0 | h0 <;>
      rcases fin2_zero_or_one (z 1) with h1 | h1 <;>
      simp [productResponse, pointMass2_expectation, contracted21,
        anchor01, pcWorld4, Function.update, h0, h1] <;> norm_num
  rw [reduced_loss_singleton anchor01 contracted21 1 0 6 hb1 ![0,0] ![1,1]
      (by simp [productResponse, pointMass2_expectation, contracted21,
        anchor01, pcWorld4, Function.update] <;> norm_num)
      (by simp [productResponse, pointMass2_expectation, contracted21,
        anchor01, pcWorld4, Function.update] <;> norm_num)]
  rw [reduced_loss_singleton anchor01 contracted21 0 0 8 hb0 ![0,1] ![0,0]
      (by simp [productResponse, pointMass2_expectation, contracted21,
        anchor01, pcWorld4, Function.update] <;> norm_num)
      (by simp [productResponse, pointMass2_expectation, contracted21,
        anchor01, pcWorld4, Function.update] <;> norm_num)]
  norm_num

theorem contracted30_gap :
    productCompressionLoss contracted30
        (productResponse (pointMass2 anchor00) contracted30) {1} -
      productCompressionLoss contracted30
        (productResponse (pointMass2 anchor00) contracted30) {0} = -1 / 2 := by
  have hb1 : ∀ z, 0 ≤ contracted30 z -
      productResponse (pointMass2 anchor00) contracted30 1 (z 1) ∧
      contracted30 z - productResponse (pointMass2 anchor00) contracted30 1 (z 1) ≤ 7 := by
    intro z
    rcases fin2_zero_or_one (z 0) with h0 | h0 <;>
      rcases fin2_zero_or_one (z 1) with h1 | h1 <;>
      simp [productResponse, pointMass2_expectation, contracted30,
        anchor00, pcWorld4, Function.update, h0, h1] <;> norm_num
  have hb0 : ∀ z, 0 ≤ contracted30 z -
      productResponse (pointMass2 anchor00) contracted30 0 (z 0) ∧
      contracted30 z - productResponse (pointMass2 anchor00) contracted30 0 (z 0) ≤ 8 := by
    intro z
    rcases fin2_zero_or_one (z 0) with h0 | h0 <;>
      rcases fin2_zero_or_one (z 1) with h1 | h1 <;>
      simp [productResponse, pointMass2_expectation, contracted30,
        anchor00, pcWorld4, Function.update, h0, h1] <;> norm_num
  rw [reduced_loss_singleton anchor00 contracted30 1 0 7 hb1 ![0,0] ![1,0]
      (by simp [productResponse, pointMass2_expectation, contracted30,
        anchor00, pcWorld4, Function.update] <;> norm_num)
      (by simp [productResponse, pointMass2_expectation, contracted30,
        anchor00, pcWorld4, Function.update] <;> norm_num)]
  rw [reduced_loss_singleton anchor00 contracted30 0 0 8 hb0 ![0,0] ![0,1]
      (by simp [productResponse, pointMass2_expectation, contracted30,
        anchor00, pcWorld4, Function.update] <;> norm_num)
      (by simp [productResponse, pointMass2_expectation, contracted30,
        anchor00, pcWorld4, Function.update] <;> norm_num)]
  norm_num

theorem contracted31_gap :
    productCompressionLoss contracted31
        (productResponse (pointMass2 anchor00) contracted31) {1} -
      productCompressionLoss contracted31
        (productResponse (pointMass2 anchor00) contracted31) {0} = -1 := by
  have hb1 : ∀ z, 0 ≤ contracted31 z -
      productResponse (pointMass2 anchor00) contracted31 1 (z 1) ∧
      contracted31 z - productResponse (pointMass2 anchor00) contracted31 1 (z 1) ≤ 6 := by
    intro z
    rcases fin2_zero_or_one (z 0) with h0 | h0 <;>
      rcases fin2_zero_or_one (z 1) with h1 | h1 <;>
      simp [productResponse, pointMass2_expectation, contracted31,
        anchor00, pcWorld4, Function.update, h0, h1] <;> norm_num
  have hb0 : ∀ z, 0 ≤ contracted31 z -
      productResponse (pointMass2 anchor00) contracted31 0 (z 0) ∧
      contracted31 z - productResponse (pointMass2 anchor00) contracted31 0 (z 0) ≤ 8 := by
    intro z
    rcases fin2_zero_or_one (z 0) with h0 | h0 <;>
      rcases fin2_zero_or_one (z 1) with h1 | h1 <;>
      simp [productResponse, pointMass2_expectation, contracted31,
        anchor00, pcWorld4, Function.update, h0, h1] <;> norm_num
  rw [reduced_loss_singleton anchor00 contracted31 1 0 6 hb1 ![0,0] ![1,0]
      (by simp [productResponse, pointMass2_expectation, contracted31,
        anchor00, pcWorld4, Function.update] <;> norm_num)
      (by simp [productResponse, pointMass2_expectation, contracted31,
        anchor00, pcWorld4, Function.update] <;> norm_num)]
  rw [reduced_loss_singleton anchor00 contracted31 0 0 8 hb0 ![0,0] ![0,1]
      (by simp [productResponse, pointMass2_expectation, contracted31,
        anchor00, pcWorld4, Function.update] <;> norm_num)
      (by simp [productResponse, pointMass2_expectation, contracted31,
        anchor00, pcWorld4, Function.update] <;> norm_num)]
  norm_num

theorem pair_contraction_all_four_choices_fail :
    17 - 4 - 13 - (-1 / 2 : ℝ) > 0 ∧
    17 - 4 - 13 - (-1 : ℝ) > 0 ∧
    17 - 4 - 13 - (-1 / 2 : ℝ) > 0 ∧
    17 - 4 - 13 - (-1 : ℝ) > 0 := by
  norm_num

theorem pair_contraction_route_killed_exact :
    IsTopKByScore (fun j ↦ osc (productResponse pointMass4 pcWorld4 j))
        selected 2 ∧
    productCompressionLoss pcWorld4 (productResponse pointMass4 pcWorld4)
        selected -
      productCompressionLoss pcWorld4 (productResponse pointMass4 pcWorld4)
        competitor = 13 ∧
    (∀ i x c, |mixedDifference pcWorld4 i x c| ≤ 13) ∧
    (17 - 4 ≤ (3 : ℝ) * 13 / 2) ∧
    17 - 4 > 13 + (-1 / 2 : ℝ) ∧
    17 - 4 > 13 + (-1 : ℝ) := by
  refine ⟨selected_is_topC, ?_, mixedDifference_le_thirteen, by norm_num,
    by norm_num, by norm_num⟩
  rw [selected_loss, competitor_loss]
  norm_num

end CIGAMF.P13.D6PairContractionCounterexample
