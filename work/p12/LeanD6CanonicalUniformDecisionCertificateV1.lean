import Mathlib
import «LeanD6PolyhedralActiveCellV1»
import «LeanD6CycleDual»

/-!
# Canonical uniform D6 certificates

This replaces the unrestricted constraint-function field of the legacy
uniform certificate by a closed syntax generated exactly by the explicit
polyhedral active-cell inequalities.
-/

namespace CIGAMF.P13.D6CanonicalUniformDecisionCertificate

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6H3Exchange
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6PolyhedralActiveCell

variable {U : Type*} [Fintype U] [Nonempty U]

/-- Closed syntax for the permitted active-cell inequality atoms. -/
inductive CanonicalConstraintAtom (n : ℕ) (U : Type*) where
  | selectedMax (z : Fin (n + 1) → U)
  | selectedMin (z : Fin (n + 1) → U)
  | competitorMax (z : Fin (n + 1) → U)
  | competitorMin (z : Fin (n + 1) → U)
  | responseMax (j : Fin (n + 1)) (u : U)
  | responseMin (j : Fin (n + 1)) (u : U)
  | topC (selectedIndex rejectedIndex : Fin (n + 1))
  deriving DecidableEq, Fintype

/-- Every atom is a linear expression oriented so that validity means it is
nonpositive.  Invalid membership combinations in the syntactic `topC` atom
evaluate to zero; the meaningful branch is exactly selected-versus-rejected. -/
noncomputable def canonicalConstraintValue {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (atom : CanonicalConstraintAtom n U)
    (F : (Fin (n + 1) → U) → ℝ) : ℝ :=
  match atom with
  | .selectedMax z =>
      retainedResidual cell.q F cell.selected z -
        retainedResidual cell.q F cell.selected cell.selectedMax
  | .selectedMin z =>
      retainedResidual cell.q F cell.selected cell.selectedMin -
        retainedResidual cell.q F cell.selected z
  | .competitorMax z =>
      retainedResidual cell.q F cell.competitor z -
        retainedResidual cell.q F cell.competitor cell.competitorMax
  | .competitorMin z =>
      retainedResidual cell.q F cell.competitor cell.competitorMin -
        retainedResidual cell.q F cell.competitor z
  | .responseMax j u =>
      productResponse cell.q F j u -
        productResponse cell.q F j (cell.responseMax j)
  | .responseMin j u =>
      productResponse cell.q F j (cell.responseMin j) -
        productResponse cell.q F j u
  | .topC i j =>
      if i ∈ cell.selected ∧ j ∉ cell.selected then
        responseWitnessSpan cell F j - responseWitnessSpan cell F i
      else 0

theorem canonicalConstraintValue_nonpos_of_polyhedral {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ)
    (hPoly : PolyhedralCellValid cell F)
    (atom : CanonicalConstraintAtom n U) :
    canonicalConstraintValue cell atom F ≤ 0 := by
  rcases hPoly with ⟨hCard, hsMax, hsMin, htMax, htMin,
    hRespMax, hRespMin, hTop⟩
  cases atom with
  | selectedMax z =>
      exact sub_nonpos.mpr (hsMax z)
  | selectedMin z =>
      exact sub_nonpos.mpr (hsMin z)
  | competitorMax z =>
      exact sub_nonpos.mpr (htMax z)
  | competitorMin z =>
      exact sub_nonpos.mpr (htMin z)
  | responseMax j u =>
      exact sub_nonpos.mpr (hRespMax j u)
  | responseMin j u =>
      exact sub_nonpos.mpr (hRespMin j u)
  | topC i j =>
      by_cases hi : i ∈ cell.selected
      · by_cases hj : j ∉ cell.selected
        · simp only [canonicalConstraintValue, hi, hj, and_self, if_true]
          exact sub_nonpos.mpr (hTop i hi j hj)
        · simp [canonicalConstraintValue, hi, hj]
      · simp [canonicalConstraintValue, hi]

/-- A nondegenerate uniform certificate with only mixed-difference atoms and
canonical active-cell constraint atoms. -/
structure CanonicalUniformDecisionCertificate {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (R J : Type*) [Fintype R] [Fintype J] where
  coordinate : R → Fin (n + 1)
  upperWorld : R → Fin (n + 1) → U
  anchorWorld : R → Fin (n + 1) → U
  alpha : R → ℝ
  constraintAtom : J → CanonicalConstraintAtom n U
  beta : J → ℝ
  beta_nonnegative : ∀ j, 0 ≤ beta j
  functional_identity : ∀ F,
    decisionLinearFunctional cell F =
      (∑ r, alpha r * cycleFunctional (coordinate r)
        (upperWorld r) (anchorWorld r) F) +
      ∑ j, beta j * canonicalConstraintValue cell (constraintAtom j) F

noncomputable def CanonicalUniformDecisionCertificate.mass {n : ℕ}
    {cell : ActiveDecisionCell n U}
    {R J : Type*} [Fintype R] [Fintype J]
    (cert : CanonicalUniformDecisionCertificate cell R J) : ℝ :=
  ∑ r, |cert.alpha r|

/-- Soundness of the restricted canonical certificate language. -/
theorem canonicalUniformDecisionCertificate_sound {n : ℕ}
    (cell : ActiveDecisionCell n U)
    {R J : Type*} [Fintype R] [Fintype J]
    (cert : CanonicalUniformDecisionCertificate cell R J)
    (F : (Fin (n + 1) → U) → ℝ)
    (delta : ℝ) (hDelta : 0 ≤ delta)
    (hCell : cell.Valid F)
    (hMixed : ∀ i x c, |mixedDifference F i x c| ≤ delta) :
    2 * (productCompressionLoss F (productResponse cell.q F) cell.selected -
      productCompressionLoss F (productResponse cell.q F) cell.competitor) ≤
      cert.mass * delta := by
  have hPoly : PolyhedralCellValid cell F :=
    (activeDecisionCell_valid_iff_polyhedral cell F).1 hCell
  have hConstraintSum :
      (∑ j, cert.beta j *
        canonicalConstraintValue cell (cert.constraintAtom j) F) ≤ 0 := by
    exact Finset.sum_nonpos fun j hj ↦
      mul_nonpos_of_nonneg_of_nonpos (cert.beta_nonnegative j)
        (canonicalConstraintValue_nonpos_of_polyhedral cell F hPoly
          (cert.constraintAtom j))
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
  unfold CanonicalUniformDecisionCertificate.mass
  calc
    (∑ r, cert.alpha r * cycleFunctional (cert.coordinate r)
          (cert.upperWorld r) (cert.anchorWorld r) F) +
        ∑ j, cert.beta j *
          canonicalConstraintValue cell (cert.constraintAtom j) F ≤
        ∑ r, cert.alpha r * cycleFunctional (cert.coordinate r)
          (cert.upperWorld r) (cert.anchorWorld r) F :=
      add_le_of_nonpos_right hConstraintSum
    _ ≤ delta * (∑ r, |cert.alpha r|) := hCycleSigned
    _ = (∑ r, |cert.alpha r|) * delta := by ring

end CIGAMF.P13.D6CanonicalUniformDecisionCertificate
