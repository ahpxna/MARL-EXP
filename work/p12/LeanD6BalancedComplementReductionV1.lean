import Mathlib
import «LeanD6SymmetricDifferenceReductionV1»
import «LeanD6OrderedAbelPAECV1»

/-!
# Reduction of the D6 headline to balanced complements

The direct endpoint-patch theorem closes every equal-cardinality competitor
except an even universe split into complementary halves.  Consequently the
headline needs only a theorem for that exceptional geometry.  This is a
strictly narrower dependency than universal PAEC existence.
-/

namespace CIGAMF.P13.D6BalancedComplementReduction

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6PAECExistence
open CIGAMF.P13.D6OrderedAbelPAEC
open CIGAMF.P13.D6SymmetricDifferenceReduction

variable {U : Type*} [Fintype U] [Nonempty U]

def EveryBalancedComplementPairHasHalfFactor {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ) : Prop :=
  ∀ (selected competitor : Finset (Fin (n + 1))) (k : ℕ),
    IsTopKByScore (fun j ↦ osc (productResponse q F j)) selected k →
    competitor.card = k →
    n + 1 = 2 * selected.card →
    Disjoint selected competitor →
    selected ∪ competitor = Finset.univ →
    productCompressionLoss F (productResponse q F) selected -
        productCompressionLoss F (productResponse q F) competitor ≤
      (n : ℝ) * delta / 2

theorem every_pair_half_factor_of_balanced_complement_core {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (hBalanced : EveryBalancedComplementPairHasHalfFactor q F delta)
    (selected competitor : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore
      (fun j ↦ osc (productResponse q F j)) selected k)
    (hCompetitorCard : competitor.card = k) :
    productCompressionLoss F (productResponse q F) selected -
        productCompressionLoss F (productResponse q F) competitor ≤
      (n : ℝ) * delta / 2 := by
  by_cases hExceptional : n + 1 = 2 * selected.card ∧
      Disjoint selected competitor ∧ selected ∪ competitor = Finset.univ
  · exact hBalanced selected competitor k hTop hCompetitorCard
      hExceptional.1 hExceptional.2.1 hExceptional.2.2
  · exact pair_half_factor_except_balanced_complement q F delta hWeight hNorm
      hDeltaNonneg hdelta selected competitor k hTop hCompetitorCard hExceptional

theorem headline_of_balanced_complement_core {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (selected : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore
      (fun j ↦ osc (productResponse q F j)) selected k)
    (hBalanced : EveryBalancedComplementPairHasHalfFactor q F delta) :
    productCompressionLoss F (productResponse q F) selected ≤
      finiteObjectiveMin (fun S ↦
        productCompressionLoss F (productResponse q F) S) k +
          (n : ℝ) * delta / 2 := by
  have hne :
      (CIGAMF.V4.ProductMixedDifference.cardinalityFamily
        (R := Fin (n + 1)) k).Nonempty :=
    ⟨selected, by
      simp [CIGAMF.V4.ProductMixedDifference.cardinalityFamily, hTop.1]⟩
  rcases finiteObjectiveMin_attained
      (fun S : Finset (Fin (n + 1)) ↦
        productCompressionLoss F (productResponse q F) S) k hne with
    ⟨optimal, hOptimalCard, hOptimalValue⟩
  have hPair := every_pair_half_factor_of_balanced_complement_core q F delta
    hWeight hNorm hDeltaNonneg hdelta hBalanced selected optimal k hTop
    hOptimalCard
  rw [← hOptimalValue]
  linarith

/- NEW-1 completely closes odd-dimensional product systems: an odd universe
cannot be partitioned into two equal complementary halves. -/
theorem headline_half_factor_of_odd_coordinate_count {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (selected : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore
      (fun j ↦ osc (productResponse q F j)) selected k)
    (hOdd : Odd (n + 1)) :
    productCompressionLoss F (productResponse q F) selected ≤
      finiteObjectiveMin (fun S ↦
        productCompressionLoss F (productResponse q F) S) k +
          (n : ℝ) * delta / 2 := by
  apply headline_of_balanced_complement_core q F delta hWeight hNorm
    hDeltaNonneg hdelta selected k hTop
  intro S T k' hTop' hcard hdim hdisj hunion
  rcases hOdd with ⟨a, ha⟩
  omega

/- For any dimension, every non-middle budget is also fully closed. -/
theorem headline_half_factor_of_nonmiddle_budget {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (selected : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore
      (fun j ↦ osc (productResponse q F j)) selected k)
    (hNotMiddle : n + 1 ≠ 2 * k) :
    productCompressionLoss F (productResponse q F) selected ≤
      finiteObjectiveMin (fun S ↦
        productCompressionLoss F (productResponse q F) S) k +
          (n : ℝ) * delta / 2 := by
  have hne :
      (CIGAMF.V4.ProductMixedDifference.cardinalityFamily
        (R := Fin (n + 1)) k).Nonempty :=
    ⟨selected, by
      simp [CIGAMF.V4.ProductMixedDifference.cardinalityFamily, hTop.1]⟩
  rcases finiteObjectiveMin_attained
      (fun S : Finset (Fin (n + 1)) ↦
        productCompressionLoss F (productResponse q F) S) k hne with
    ⟨optimal, hOptimalCard, hOptimalValue⟩
  have hNotExceptional : ¬(n + 1 = 2 * selected.card ∧
      Disjoint selected optimal ∧ selected ∪ optimal = Finset.univ) := by
    intro hExceptional
    apply hNotMiddle
    rw [← hTop.1]
    exact hExceptional.1
  have hPair := pair_half_factor_except_balanced_complement q F delta hWeight
    hNorm hDeltaNonneg hdelta selected optimal k hTop hOptimalCard
    hNotExceptional
  rw [← hOptimalValue]
  linarith

/- Ordered-Abel PAEC data is one sufficient way to close only the exceptional
balanced-complement branch.  Constructing this data from arbitrary active
extrema and product-reference consistency remains the live theorem. -/
theorem balanced_core_of_ordered_Abel_PAEC {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (hConstruct : ∀ (selected competitor : Finset (Fin (n + 1))) (k : ℕ),
      IsTopKByScore (fun j ↦ osc (productResponse q F j)) selected k →
      competitor.card = k →
      n + 1 = 2 * selected.card →
      Disjoint selected competitor →
      selected ∪ competitor = Finset.univ →
      HasOrderedAbelPAEC q F selected competitor) :
    EveryBalancedComplementPairHasHalfFactor q F delta := by
  intro selected competitor k hTop hcard hdim hdisj hunion
  have hPAEC := orderedAbelPAEC_to_hasPAEC q F selected competitor
    (hConstruct selected competitor k hTop hcard hdim hdisj hunion)
  exact pair_half_factor_of_hasPAEC q F selected competitor delta
    hDeltaNonneg hdelta hPAEC

end CIGAMF.P13.D6BalancedComplementReduction
