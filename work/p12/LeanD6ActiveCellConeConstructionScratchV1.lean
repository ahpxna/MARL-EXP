import Mathlib
import «LeanD6BalancedProductCoreScratchV1»
import «LeanD6CanonicalPolyhedralCellsV1»
import «LeanD6Fin6GammaFiveSaturationV1»

/-!
# Noncircular selector two-path candidate for active-cell cone completion

This scratch file deliberately starts before a certificate is supplied.  For
an arbitrary active cell it forms the literal two selected-coordinate paths
from the fixed selected residual extrema to the fixed response extrema.  The
resulting remainder is an exact functional, not a post-hoc definition from a
certificate.

The Fin-4 calculation below records an exact obstruction to treating this
fixed two-path expression as the universal mass-`n` construction: its raw
path has four nontrivial selected-coordinate steps while `n = 3`.  This does
not refute cone completion or the normalized balanced law; the existing
three-cycle Fin-4 certificate is a different recombined certificate.
-/

namespace CIGAMF.P13.D6ActiveCellConeConstructionScratch

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6H3Exchange
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6BalancedProductCoreScratch
open CIGAMF.P13.D6CanonicalPolyhedralCells
open CIGAMF.P13.D6PAECFin4
open CIGAMF.P13.D6Fin6GammaFiveSaturation

variable {U : Type*} [Fintype U] [Nonempty U]

/-- The noncircular two-path cycle expression determined solely by the
selectors stored in an active cell. -/
noncomputable def selectorTwoPathCyclePart {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ) : ℝ :=
  pairedEndpointCycleAverage cell.q F
    cell.selectedMax cell.responseMax
    cell.selectedMin cell.responseMin
    (canonicalPatchOrder cell.selected)

/-- The exact remainder after the selector-determined two-path cycle part.
Unlike the earlier `canonicalRemainder`, this definition does not receive a
certificate as an argument. -/
noncomputable def selectorTwoPathRemainder {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ) : ℝ :=
  decisionLinearFunctional cell F - selectorTwoPathCyclePart cell F

/-- The raw coefficient budget of this literal construction: one product
cycle average for each selected coordinate at each endpoint.  It is only a
syntactic budget; cancellations or a different cone representation may lower
the actual certificate mass. -/
noncomputable def selectorTwoPathRawMass {n : ℕ}
    (cell : ActiveDecisionCell n U) : ℝ :=
  2 * cell.selected.card

theorem decisionLinearFunctional_eq_selectorTwoPath_add_remainder {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ) :
    decisionLinearFunctional cell F =
      selectorTwoPathCyclePart cell F + selectorTwoPathRemainder cell F := by
  unfold selectorTwoPathRemainder
  ring

/-- This is the actual selector-level two-path identity.  It is the object
whose cone membership would need to be proved constructively for the new
route; no sign condition is asserted here. -/
theorem selectorTwoPathRemainder_eq_explicit {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ)
    (hNorm : ∑ c, jointWeight cell.q c = 1) :
    selectorTwoPathRemainder cell F =
      retainedResidual cell.q F cell.selected
          (patchCoordinates cell.selectedMax cell.responseMax cell.selected) -
        retainedResidual cell.q F cell.selected
          (patchCoordinates cell.selectedMin cell.responseMin cell.selected) -
        retainedResidual cell.q F cell.competitor cell.competitorMax +
        retainedResidual cell.q F cell.competitor cell.competitorMin := by
  have hPath := pairedEndpointPatch_eq_canonical_cycleAverage cell.q F
    cell.selected cell.selected (by rfl)
    cell.selectedMax cell.responseMax cell.selectedMin cell.responseMin hNorm
  unfold selectorTwoPathRemainder selectorTwoPathCyclePart
    decisionLinearFunctional
  linarith

/-- In the canonical Fin-4 cell both selected coordinates change at both
endpoint paths.  Thus the literal two-path construction has no zero step to
remove before a genuinely new recombination argument is supplied. -/
theorem canonicalCell4_upper_selected_steps_nontrivial :
    ∀ i ∈ selected4,
      canonicalCell4.selectedMax i ≠ canonicalCell4.responseMax i := by
  intro i hi
  fin_cases i <;> simp_all [canonicalCell4, selected4, s4, a4]

theorem canonicalCell4_lower_selected_steps_nontrivial :
    ∀ i ∈ selected4,
      canonicalCell4.selectedMin i ≠ canonicalCell4.responseMin i := by
  intro i hi
  fin_cases i <;> simp_all [canonicalCell4, selected4, t4, a4]

theorem canonicalCell4_selectorTwoPath_rawMass :
    selectorTwoPathRawMass canonicalCell4 = 4 := by
  norm_num [selectorTwoPathRawMass, canonicalCell4, selected4]

theorem canonicalCell4_selectorTwoPath_rawMass_exceeds_target :
    (3 : ℝ) < selectorTwoPathRawMass canonicalCell4 := by
  rw [canonicalCell4_selectorTwoPath_rawMass]
  norm_num

/-- By contrast, the exact Gamma-five Fin-6 cell has at least one degenerate
lower-endpoint update in this same raw construction.  This records that path
morphology varies across cells, so a fixed tree/leaf-removal template cannot
be inferred from the Fin-4 example. -/
theorem gammaFive_lower_step_one_is_degenerate :
    gammaFiveCell.selectedMin (1 : Fin 6) =
      gammaFiveCell.responseMin (1 : Fin 6) := by
  norm_num [gammaFiveCell, gammaFiveSelectedMin, gammaFiveResponseMin, a6]

end CIGAMF.P13.D6ActiveCellConeConstructionScratch
