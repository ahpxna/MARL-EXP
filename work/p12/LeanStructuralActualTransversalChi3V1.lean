import Mathlib
import «LeanStructuralMinimumTransversalWidthV1»
import «LeanStructuralPrefixCoverChi3ProofAttemptV1»

/-!
# Actual support-oscillation lower bound in transversal language

This adapter does not change the established five-relation witness.  It
transports its compiled `chi_prefix >= 3` result through the exact S3
prefix-chain transversal characterization.  Thus the new poset formulation
is attached to an actual `selectedRadius` instance rather than only an
abstract set objective.
-/

namespace CIGAMF.P13.StructuralActualTransversalChi3

open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralPrefixCoverWitnesses
open CIGAMF.P13.StructuralPrefixCoverChi3ProofAttempt
open CIGAMF.P13.StructuralMinimumTransversalWidth

theorem actual_supportOsc_transversal_width_not_at_most_two :
    ¬ TransversalPrefixWidthAtMost (selectedRadius chi3F) 0 2 := by
  intro hWidth
  apply STRUCT_CHI3_prefix_cover_not_at_most_two
  exact
    (S3_prefix_dimension_iff_minimum_transversal_prefix_width
      (selectedRadius chi3F) 0 2).2 hWidth

theorem actual_supportOsc_prefix_dimension_at_least_three :
    ∀ K, PrefixCoverDimensionAtMost (selectedRadius chi3F) 0 K → 3 ≤ K := by
  intro K hK
  by_contra hNot
  have hK2 : K ≤ 2 := by omega
  apply STRUCT_CHI3_prefix_cover_not_at_most_two
  rcases hK with ⟨menu, hCard, hCover⟩
  exact ⟨menu, hCard.trans hK2, hCover⟩

end CIGAMF.P13.StructuralActualTransversalChi3
