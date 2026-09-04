import Mathlib
import «LeanD6CycleDual»

/-!
# Finite LP-dual / cycle certificate connector

This module does not assume that every balanced D6 branch has a certificate.
It proves the exact reusable implication needed after an LP-discovered sparse
decomposition has been translated into Lean: nonnegative Top-C/endpoint slack
plus bounded cycle mass yields the corresponding decision bound.
-/

namespace CIGAMF.P13.D6BalancedCycleCertificate

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual

variable {U : Type*} [Fintype U] [Nonempty U]

theorem decision_le_cycle_budget
    {R Top End : Type*} [Fintype R] [Fintype Top] [Fintype End]
    {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (decisionGap delta mass : ℝ)
    (i : R → Fin (n + 1))
    (x c : R → Fin (n + 1) → U)
    (alpha : R → ℝ)
    (topSlack beta : Top → ℝ)
    (endpointSlack gamma : End → ℝ)
    (hdeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ r, |mixedDifference F (i r) (x r) (c r)| ≤ delta)
    (hTopSlack : ∀ s, 0 ≤ topSlack s)
    (hBeta : ∀ s, 0 ≤ beta s)
    (hEndpointSlack : ∀ t, 0 ≤ endpointSlack t)
    (hGamma : ∀ t, 0 ≤ gamma t)
    (hDecomp :
      decisionGap + (∑ s, beta s * topSlack s) +
          (∑ t, gamma t * endpointSlack t) =
        ∑ r, alpha r * cycleFunctional (i r) (x r) (c r) F)
    (hMass : ∑ r, |alpha r| ≤ mass) :
    decisionGap ≤ delta * mass := by
  have hTopNonneg : 0 ≤ ∑ s, beta s * topSlack s := by
    exact Finset.sum_nonneg (fun s hs ↦
      mul_nonneg (hBeta s) (hTopSlack s))
  have hEndNonneg : 0 ≤ ∑ t, gamma t * endpointSlack t := by
    exact Finset.sum_nonneg (fun t ht ↦
      mul_nonneg (hGamma t) (hEndpointSlack t))
  have hDecisionToSigned :
      decisionGap ≤ ∑ r, alpha r * cycleFunctional (i r) (x r) (c r) F := by
    linarith
  have hSignedToAbs :
      (∑ r, alpha r * cycleFunctional (i r) (x r) (c r) F) ≤
        |∑ r, alpha r * cycleFunctional (i r) (x r) (c r) F| :=
    le_abs_self _
  have hCycle := finite_cycle_combination_bound F delta i x c alpha hdelta
  have hScale : delta * (∑ r, |alpha r|) ≤ delta * mass :=
    mul_le_mul_of_nonneg_left hMass hdeltaNonneg
  exact le_trans hDecisionToSigned
    (le_trans hSignedToAbs (le_trans hCycle hScale))

/- Normalization used by the D6 half-factor target when a certificate for the
unscaled decision gap has cycle mass at most `(m-1)/2 = n/2`. -/
theorem decision_half_factor_of_cycle_certificate
    {R Top End : Type*} [Fintype R] [Fintype Top] [Fintype End]
    {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (decisionGap delta : ℝ)
    (i : R → Fin (n + 1))
    (x c : R → Fin (n + 1) → U)
    (alpha : R → ℝ)
    (topSlack beta : Top → ℝ)
    (endpointSlack gamma : End → ℝ)
    (hdeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ r, |mixedDifference F (i r) (x r) (c r)| ≤ delta)
    (hTopSlack : ∀ s, 0 ≤ topSlack s)
    (hBeta : ∀ s, 0 ≤ beta s)
    (hEndpointSlack : ∀ t, 0 ≤ endpointSlack t)
    (hGamma : ∀ t, 0 ≤ gamma t)
    (hDecomp :
      decisionGap + (∑ s, beta s * topSlack s) +
          (∑ t, gamma t * endpointSlack t) =
        ∑ r, alpha r * cycleFunctional (i r) (x r) (c r) F)
    (hMass : ∑ r, |alpha r| ≤ (n : ℝ) / 2) :
    decisionGap ≤ (n : ℝ) * delta / 2 := by
  have h := decision_le_cycle_budget F decisionGap delta ((n : ℝ) / 2)
    i x c alpha topSlack beta endpointSlack gamma hdeltaNonneg hdelta
    hTopSlack hBeta hEndpointSlack hGamma hDecomp hMass
  nlinarith

/- Direct D6 specialization: once a symbolic branch decomposition has the
actual selected-vs-competitor compression gap on its left, no further bridge
from LP dual algebra to the scientific loss is missing. -/
theorem productCompressionLoss_half_factor_of_cycle_certificate
    {R Top End : Type*} [Fintype R] [Fintype Top] [Fintype End]
    {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (delta : ℝ)
    (i : R → Fin (n + 1))
    (x c : R → Fin (n + 1) → U)
    (alpha : R → ℝ)
    (topSlack beta : Top → ℝ)
    (endpointSlack gamma : End → ℝ)
    (hdeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ r, |mixedDifference F (i r) (x r) (c r)| ≤ delta)
    (hTopSlack : ∀ s, 0 ≤ topSlack s)
    (hBeta : ∀ s, 0 ≤ beta s)
    (hEndpointSlack : ∀ t, 0 ≤ endpointSlack t)
    (hGamma : ∀ t, 0 ≤ gamma t)
    (hDecomp :
      (productCompressionLoss F (productResponse q F) selected -
          productCompressionLoss F (productResponse q F) competitor) +
          (∑ s, beta s * topSlack s) +
          (∑ t, gamma t * endpointSlack t) =
        ∑ r, alpha r * cycleFunctional (i r) (x r) (c r) F)
    (hMass : ∑ r, |alpha r| ≤ (n : ℝ) / 2) :
    productCompressionLoss F (productResponse q F) selected -
        productCompressionLoss F (productResponse q F) competitor ≤
      (n : ℝ) * delta / 2 := by
  exact decision_half_factor_of_cycle_certificate F
    (productCompressionLoss F (productResponse q F) selected -
      productCompressionLoss F (productResponse q F) competitor)
    delta i x c alpha topSlack beta endpointSlack gamma hdeltaNonneg hdelta
    hTopSlack hBeta hEndpointSlack hGamma hDecomp hMass

/-! ## PAEC normalization

The LP discoveries use the doubled decision gap.  In this normalization a
sharp certificate pays at most `n = m - 1` units of cycle mass; all Top-C and
active-endpoint corrections occur on the right with nonpositive sign. -/

theorem balanced_direct_of_PAEC
    {R Top End : Type*} [Fintype R] [Fintype Top] [Fintype End]
    {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (decisionGap delta : ℝ)
    (i : R → Fin (n + 1))
    (x c : R → Fin (n + 1) → U)
    (alpha : R → ℝ)
    (topCorrection : Top → ℝ)
    (endpointCorrection : End → ℝ)
    (hdeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ r, |mixedDifference F (i r) (x r) (c r)| ≤ delta)
    (hTop : ∑ s, topCorrection s ≤ 0)
    (hEndpoint : ∑ t, endpointCorrection t ≤ 0)
    (hCertificate :
      2 * decisionGap ≤
        (∑ r, alpha r * cycleFunctional (i r) (x r) (c r) F) +
          (∑ s, topCorrection s) +
          (∑ t, endpointCorrection t))
    (hMass : ∑ r, |alpha r| ≤ (n : ℝ)) :
    decisionGap ≤ (n : ℝ) * delta / 2 := by
  have hCycle := finite_cycle_combination_bound F delta i x c alpha hdelta
  have hScale : delta * (∑ r, |alpha r|) ≤ delta * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hMass hdeltaNonneg
  have hSigned :
      (∑ r, alpha r * cycleFunctional (i r) (x r) (c r) F) ≤
        delta * (n : ℝ) := by
    calc
      (∑ r, alpha r * cycleFunctional (i r) (x r) (c r) F)
          ≤ |∑ r, alpha r * cycleFunctional (i r) (x r) (c r) F| :=
            le_abs_self _
      _ ≤ delta * (∑ r, |alpha r|) := hCycle
      _ ≤ delta * (n : ℝ) := hScale
  nlinarith

theorem productCompressionLoss_half_factor_of_PAEC
    {R Top End : Type*} [Fintype R] [Fintype Top] [Fintype End]
    {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (delta : ℝ)
    (i : R → Fin (n + 1))
    (x c : R → Fin (n + 1) → U)
    (alpha : R → ℝ)
    (topCorrection : Top → ℝ)
    (endpointCorrection : End → ℝ)
    (hdeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ r, |mixedDifference F (i r) (x r) (c r)| ≤ delta)
    (hTop : ∑ s, topCorrection s ≤ 0)
    (hEndpoint : ∑ t, endpointCorrection t ≤ 0)
    (hCertificate :
      2 * (productCompressionLoss F (productResponse q F) selected -
          productCompressionLoss F (productResponse q F) competitor) ≤
        (∑ r, alpha r * cycleFunctional (i r) (x r) (c r) F) +
          (∑ s, topCorrection s) +
          (∑ t, endpointCorrection t))
    (hMass : ∑ r, |alpha r| ≤ (n : ℝ)) :
    productCompressionLoss F (productResponse q F) selected -
        productCompressionLoss F (productResponse q F) competitor ≤
      (n : ℝ) * delta / 2 := by
  exact balanced_direct_of_PAEC F
    (productCompressionLoss F (productResponse q F) selected -
      productCompressionLoss F (productResponse q F) competitor)
    delta i x c alpha topCorrection endpointCorrection hdeltaNonneg hdelta
    hTop hEndpoint hCertificate hMass

end CIGAMF.P13.D6BalancedCycleCertificate
