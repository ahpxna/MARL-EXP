import Mathlib
import «LeanD6PAECExistence»
import «LeanD6AbelSurplusV1»

/-!
# Ordered Abel PAEC interface

This file isolates the exact remaining constructive obligation.  An ordered
two-path construction must supply actual D6 cycle atoms and an equality or
inequality whose correction is the Abel-weighted Top-C surplus.  Once that
data exists, the correction sign and `HasPAECForPair` follow automatically.

No arbitrary Top-C-to-PAEC existence claim is assumed here.
-/

namespace CIGAMF.P13.D6OrderedAbelPAEC

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6PAECExistence
open CIGAMF.P13.D6AbelSurplus

variable {U : Type*} [Fintype U] [Nonempty U]

def HasOrderedAbelPAEC {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1))) : Prop :=
  ∃ pairCount atomCount : ℕ,
    ∃ coord : Fin atomCount → Fin (n + 1),
    ∃ upperWorld anchorWorld : Fin atomCount → Fin (n + 1) → U,
    ∃ alpha : Fin atomCount → ℝ,
    ∃ surplus weight : ℕ → ℝ,
      0 < pairCount ∧
      (∀ r, r ≤ pairCount → 0 ≤ prefixSum surplus r) ∧
      0 ≤ weight (pairCount - 1) ∧
      (∀ i, i + 1 < pairCount → weight (i + 1) ≤ weight i) ∧
      2 * (productCompressionLoss F (productResponse q F) selected -
        productCompressionLoss F (productResponse q F) competitor) ≤
        (∑ a, alpha a *
          cycleFunctional (coord a) (upperWorld a) (anchorWorld a) F) +
          abelCorrection surplus weight (pairCount - 1) ∧
      (∑ a, |alpha a|) ≤ (n : ℝ)

theorem orderedAbelPAEC_to_hasPAEC {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (D : HasOrderedAbelPAEC q F selected competitor) :
    HasPAECForPair q F selected competitor := by
  rcases D with ⟨pairCount, atomCount, coord, upperWorld, anchorWorld,
    alpha, surplus, weight, hpos, hPrefix, hLast, hMono, hCertificate, hMass⟩
  have hCorrection :
      abelCorrection surplus weight (pairCount - 1) ≤ 0 := by
    apply abelCorrection_nonpositive
    · intro r hr
      have hEq : pairCount - 1 + 1 = pairCount := by omega
      rw [hEq] at hr
      exact hPrefix r hr
    · exact hLast
    · intro i hi
      exact hMono i (by omega)
  exact ⟨atomCount, coord, upperWorld, anchorWorld, alpha,
    abelCorrection surplus weight (pairCount - 1), hCorrection,
    hCertificate, hMass⟩

/- This is the precise universal construction still needed for the D6
headline.  It is a named interface, not an assumed theorem. -/
def EveryTopCPairHasOrderedAbelPAEC {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected : Finset (Fin (n + 1))) (k : ℕ) : Prop :=
  IsTopKByScore (fun j ↦ osc (productResponse q F j)) selected k ∧
    ∀ competitor : Finset (Fin (n + 1)), competitor.card = k →
      HasOrderedAbelPAEC q F selected competitor

theorem orderedAbel_family_implies_every_PAEC {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected : Finset (Fin (n + 1))) (k : ℕ)
    (h : EveryTopCPairHasOrderedAbelPAEC q F selected k) :
    EveryTopCPairHasPAEC q F selected k := by
  refine ⟨h.1, ?_⟩
  intro competitor hcard
  exact orderedAbelPAEC_to_hasPAEC q F selected competitor
    (h.2 competitor hcard)

end CIGAMF.P13.D6OrderedAbelPAEC
