import Mathlib
import «LeanD6CanonicalPathRemainderV1»

/-!
# Active-cell cone classification of a canonical remainder

For a supplied canonical certificate, the remainder is exactly a nonnegative
combination of the closed active-cell constraint syntax.  This is the cone
statement, not the false statement that an older raw correction is always
nonpositive.  It does not assert that every balanced cell already has such a
certificate; that existence problem is isolated in the next module.
-/

namespace CIGAMF.P13.D6ActiveCellRemainderDecomposition

open scoped BigOperators
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6PolyhedralActiveCell
open CIGAMF.P13.D6CanonicalUniformDecisionCertificate
open CIGAMF.P13.D6CanonicalPathRemainder

variable {U : Type*} [Fintype U] [Nonempty U]

theorem canonicalRemainder_eq_active_cell_cone {n : ℕ}
    {cell : ActiveDecisionCell n U}
    {R J : Type*} [Fintype R] [Fintype J]
    (cert : CanonicalUniformDecisionCertificate cell R J)
    (F : (Fin (n + 1) → U) → ℝ) :
    canonicalRemainder cert F =
      ∑ j, cert.beta j *
        canonicalConstraintValue cell (cert.constraintAtom j) F ∧
      ∀ j, 0 ≤ cert.beta j := by
  exact ⟨rfl, cert.beta_nonnegative⟩

theorem canonicalRemainder_nonpos_of_valid_cell {n : ℕ}
    {cell : ActiveDecisionCell n U}
    {R J : Type*} [Fintype R] [Fintype J]
    (cert : CanonicalUniformDecisionCertificate cell R J)
    (F : (Fin (n + 1) → U) → ℝ)
    (hCell : cell.Valid F) :
    canonicalRemainder cert F ≤ 0 := by
  have hPoly : PolyhedralCellValid cell F :=
    (activeDecisionCell_valid_iff_polyhedral cell F).1 hCell
  unfold canonicalRemainder
  exact Finset.sum_nonpos fun j hj ↦
    mul_nonpos_of_nonneg_of_nonpos (cert.beta_nonnegative j)
      (canonicalConstraintValue_nonpos_of_polyhedral cell F hPoly
        (cert.constraintAtom j))

end CIGAMF.P13.D6ActiveCellRemainderDecomposition
