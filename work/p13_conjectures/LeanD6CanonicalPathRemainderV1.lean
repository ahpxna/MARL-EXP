import Mathlib
import «LeanD6CanonicalUniformDecisionCertificateV1»

/-!
# Canonical cycle part and active-cell remainder

This file exposes the two pieces already present in a canonical uniform
certificate.  It deliberately makes no raw sign claim: the remainder is the
active-cell cone term and is controlled only through canonical inequalities.
-/

namespace CIGAMF.P13.D6CanonicalPathRemainder

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6CanonicalUniformDecisionCertificate

variable {U : Type*} [Fintype U] [Nonempty U]

noncomputable def canonicalCyclePart {n : ℕ}
    {cell : ActiveDecisionCell n U}
    {R J : Type*} [Fintype R] [Fintype J]
    (cert : CanonicalUniformDecisionCertificate cell R J)
    (F : (Fin (n + 1) → U) → ℝ) : ℝ :=
  ∑ r, cert.alpha r * cycleFunctional (cert.coordinate r)
    (cert.upperWorld r) (cert.anchorWorld r) F

noncomputable def canonicalRemainder {n : ℕ}
    {cell : ActiveDecisionCell n U}
    {R J : Type*} [Fintype R] [Fintype J]
    (cert : CanonicalUniformDecisionCertificate cell R J)
    (F : (Fin (n + 1) → U) → ℝ) : ℝ :=
  ∑ j, cert.beta j *
    canonicalConstraintValue cell (cert.constraintAtom j) F

theorem decisionLinearFunctional_eq_cyclePart_add_remainder {n : ℕ}
    {cell : ActiveDecisionCell n U}
    {R J : Type*} [Fintype R] [Fintype J]
    (cert : CanonicalUniformDecisionCertificate cell R J)
    (F : (Fin (n + 1) → U) → ℝ) :
    decisionLinearFunctional cell F =
      canonicalCyclePart cert F + canonicalRemainder cert F := by
  exact cert.functional_identity F

theorem canonicalCyclePart_le_mass_mul_delta {n : ℕ}
    {cell : ActiveDecisionCell n U}
    {R J : Type*} [Fintype R] [Fintype J]
    (cert : CanonicalUniformDecisionCertificate cell R J)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hMixed : ∀ i x c, |mixedDifference F i x c| ≤ delta) :
    canonicalCyclePart cert F ≤ cert.mass * delta := by
  have h := finite_cycle_combination_bound F delta cert.coordinate
    cert.upperWorld cert.anchorWorld cert.alpha
    (fun r ↦ hMixed (cert.coordinate r) (cert.upperWorld r)
      (cert.anchorWorld r))
  have hSigned : canonicalCyclePart cert F ≤
      |canonicalCyclePart cert F| := le_abs_self _
  calc
    canonicalCyclePart cert F ≤ |canonicalCyclePart cert F| := hSigned
    _ ≤ delta * cert.mass := by
      simpa [canonicalCyclePart,
        CanonicalUniformDecisionCertificate.mass] using h
    _ = cert.mass * delta := by ring

end CIGAMF.P13.D6CanonicalPathRemainder
