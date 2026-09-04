import Mathlib
import «LeanD6BalancedCycleCertificate»
import «LeanD6HalfFactorCore»

/-!
# Exact PAEC existence interface for the remaining universal blocker

This file does not assume a canonical active-extrema branch.  It states the
literal certificate that must be constructed for every equal-cardinality
Top-C comparison, and proves that this construction closes the existing D6
headline.  The existence theorem itself remains the research target.
-/

namespace CIGAMF.P13.D6PAECExistence

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6BalancedCycleCertificate

variable {U : Type*} [Fintype U] [Nonempty U]

def HasPAECForPair {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1))) : Prop :=
  ∃ r : ℕ,
    ∃ i : Fin r → Fin (n + 1),
    ∃ x c : Fin r → Fin (n + 1) → U,
    ∃ alpha : Fin r → ℝ,
    ∃ correction : ℝ,
      correction ≤ 0 ∧
      2 * (productCompressionLoss F (productResponse q F) selected -
          productCompressionLoss F (productResponse q F) competitor) ≤
        (∑ a, alpha a * cycleFunctional (i a) (x a) (c a) F) +
          correction ∧
      (∑ a, |alpha a|) ≤ (n : ℝ)

theorem pair_half_factor_of_hasPAEC {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (delta : ℝ)
    (hdeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ i x c, |mixedDifference F i x c| ≤ delta)
    (hPAEC : HasPAECForPair q F selected competitor) :
    productCompressionLoss F (productResponse q F) selected -
        productCompressionLoss F (productResponse q F) competitor ≤
      (n : ℝ) * delta / 2 := by
  rcases hPAEC with ⟨r, i, x, c, alpha, correction,
    hCorrection, hCertificate, hMass⟩
  have hCycle := finite_cycle_combination_bound F delta i x c alpha
    (fun a ↦ hdelta (i a) (x a) (c a))
  have hScale : delta * (∑ a, |alpha a|) ≤ delta * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hMass hdeltaNonneg
  have hSigned :
      (∑ a, alpha a * cycleFunctional (i a) (x a) (c a) F) ≤
        delta * (n : ℝ) := by
    calc
      _ ≤ |∑ a, alpha a * cycleFunctional (i a) (x a) (c a) F| :=
        le_abs_self _
      _ ≤ delta * (∑ a, |alpha a|) := hCycle
      _ ≤ delta * (n : ℝ) := hScale
  nlinarith

def EveryTopCPairHasPAEC {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected : Finset (Fin (n + 1))) (k : ℕ) : Prop :=
  IsTopKByScore (fun j ↦ osc (productResponse q F j)) selected k ∧
    ∀ competitor : Finset (Fin (n + 1)), competitor.card = k →
      HasPAECForPair q F selected competitor

/- This theorem identifies the exact missing implication: once arbitrary
Top-C/equal-cardinality pairs produce a PAEC, the finite minimizer connector
closes without any new scientific assumption. -/
theorem headline_of_every_topC_pair_has_PAEC {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hdeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ i x c, |mixedDifference F i x c| ≤ delta)
    (selected : Finset (Fin (n + 1))) (k : ℕ)
    (hEvery : EveryTopCPairHasPAEC q F selected k) :
    productCompressionLoss F (productResponse q F) selected ≤
      finiteObjectiveMin (fun S ↦
        productCompressionLoss F (productResponse q F) S) k +
          (n : ℝ) * delta / 2 := by
  have hne :
      (CIGAMF.V4.ProductMixedDifference.cardinalityFamily
        (R := Fin (n + 1)) k).Nonempty :=
    ⟨selected, by
      simp [CIGAMF.V4.ProductMixedDifference.cardinalityFamily,
        hEvery.1.1]⟩
  rcases finiteObjectiveMin_attained
      (fun S : Finset (Fin (n + 1)) ↦
        productCompressionLoss F (productResponse q F) S) k hne with
    ⟨optimal, hOptimalCard, hOptimalValue⟩
  have hPair := pair_half_factor_of_hasPAEC q F selected optimal delta
    hdeltaNonneg hdelta (hEvery.2 optimal hOptimalCard)
  rw [← hOptimalValue]
  linarith

end CIGAMF.P13.D6PAECExistence
