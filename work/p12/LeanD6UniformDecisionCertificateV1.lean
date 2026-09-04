import Mathlib
import «LeanD6ActiveDecisionCellV1»
import «LeanD6CycleDual»

/-!
# Uniform functional-level decision certificates

Unlike the legacy instance-wise PAEC mass, the identity in a uniform
certificate holds for every numerical world function.  Coefficients therefore
represent the active decision cell as a linear functional before observing a
particular `F`.
-/

namespace CIGAMF.P13.D6UniformDecisionCertificate

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6ActiveDecisionCell

variable {U : Type*} [Fintype U] [Nonempty U]

structure UniformDecisionCertificate {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (R J : Type*) [Fintype R] [Fintype J] where
  coordinate : R → Fin (n + 1)
  upperWorld : R → Fin (n + 1) → U
  anchorWorld : R → Fin (n + 1) → U
  alpha : R → ℝ
  constraint : J → ((Fin (n + 1) → U) → ℝ) → ℝ
  beta : J → ℝ
  beta_nonnegative : ∀ j, 0 ≤ beta j
  functional_identity : ∀ F,
    decisionLinearFunctional cell F =
      (∑ r, alpha r * cycleFunctional (coordinate r)
        (upperWorld r) (anchorWorld r) F) +
      ∑ j, beta j * constraint j F

noncomputable def UniformDecisionCertificate.mass {n : ℕ}
    {cell : ActiveDecisionCell n U}
    {R J : Type*} [Fintype R] [Fintype J]
    (cert : UniformDecisionCertificate cell R J) : ℝ :=
  ∑ r, |cert.alpha r|

def ConstraintsValid {n : ℕ}
    {cell : ActiveDecisionCell n U}
    {R J : Type*} [Fintype R] [Fintype J]
    (cert : UniformDecisionCertificate cell R J)
    (F : (Fin (n + 1) → U) → ℝ) : Prop :=
  ∀ j, cert.constraint j F ≤ 0

/-- Soundness of the new nondegenerate certificate language.  The scientific
constraints may encode active-extremum and Top-C inequalities, but their sign
is explicit rather than hidden in an instance-wise correction scalar. -/
theorem uniformDecisionCertificate_sound {n : ℕ}
    (cell : ActiveDecisionCell n U)
    {R J : Type*} [Fintype R] [Fintype J]
    (cert : UniformDecisionCertificate cell R J)
    (F : (Fin (n + 1) → U) → ℝ)
    (delta : ℝ) (hDelta : 0 ≤ delta)
    (hCell : cell.Valid F)
    (hConstraints : ConstraintsValid cert F)
    (hMixed : ∀ i x c, |mixedDifference F i x c| ≤ delta) :
    2 * (productCompressionLoss F (productResponse cell.q F) cell.selected -
      productCompressionLoss F (productResponse cell.q F) cell.competitor) ≤
      cert.mass * delta := by
  have hConstraintSum :
      (∑ j, cert.beta j * cert.constraint j F) ≤ 0 := by
    exact Finset.sum_nonpos fun j hj ↦
      mul_nonpos_of_nonneg_of_nonpos (cert.beta_nonnegative j)
        (hConstraints j)
  have hCycles := finite_cycle_combination_bound F delta cert.coordinate
    cert.upperWorld cert.anchorWorld cert.alpha
    (fun r ↦ hMixed (cert.coordinate r) (cert.upperWorld r)
      (cert.anchorWorld r))
  have hCycleSigned :
      (∑ r, cert.alpha r * cycleFunctional (cert.coordinate r)
        (cert.upperWorld r) (cert.anchorWorld r) F) ≤
      delta * cert.mass := by
    exact (le_abs_self _).trans hCycles
  rw [doubledDecisionGap_eq_linear cell F hCell]
  change decisionLinearFunctional cell F ≤ cert.mass * delta
  rw [cert.functional_identity F]
  unfold UniformDecisionCertificate.mass
  calc
    (∑ r, cert.alpha r * cycleFunctional (cert.coordinate r)
          (cert.upperWorld r) (cert.anchorWorld r) F) +
        ∑ j, cert.beta j * cert.constraint j F ≤
        ∑ r, cert.alpha r * cycleFunctional (cert.coordinate r)
          (cert.upperWorld r) (cert.anchorWorld r) F :=
      add_le_of_nonpos_right hConstraintSum
    _ ≤ delta * (∑ r, |cert.alpha r|) := hCycleSigned
    _ = (∑ r, |cert.alpha r|) * delta := by ring

end CIGAMF.P13.D6UniformDecisionCertificate
