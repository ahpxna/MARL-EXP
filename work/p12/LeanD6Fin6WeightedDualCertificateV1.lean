import Mathlib
import «LeanD6Fin6GammaFiveSaturationV1»
import «LeanD6CanonicalUniformDecisionCertificateV1»
import «LeanD6CanonicalPolyhedralCellsV1»

/-!
# Exact weighted six-cycle certificate for the Gamma-five Fin-6 cell

This is the exact rational dual certificate attached to the authoritative
active-cell LP witness.  Its six cycle coefficients have absolute masses
`1/2, 1/2, 1, 3/2, 1/2, 1`, hence total mass five.  The result is specific to
this frozen active cell and does not assert the open universal balanced-cell
theorem.
-/

namespace CIGAMF.P13.D6Fin6WeightedDualCertificate

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6H3Exchange
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6PolyhedralActiveCell
open CIGAMF.P13.D6CanonicalUniformDecisionCertificate
open CIGAMF.P13.D6DecisionInteractionComplexity
open CIGAMF.P13.D6CanonicalPolyhedralCells
open CIGAMF.P13.D6PAECFin6
open CIGAMF.P13.D6Fin6GammaFiveSaturation

private def w0110 : Fin 6 → Fin 2 := a6 0 0 0 1 1 0
private def w001100 : Fin 6 → Fin 2 := a6 0 0 1 1 0 0
private def w010110 : Fin 6 → Fin 2 := a6 0 1 0 1 1 0
private def w011110 : Fin 6 → Fin 2 := a6 0 1 1 1 1 0
private def w101000 : Fin 6 → Fin 2 := a6 1 0 1 0 0 0

@[simp] private theorem a6_at0 (a b c d e f : Fin 2) :
    a6 a b c d e f 0 = a := by rfl
@[simp] private theorem a6_at1 (a b c d e f : Fin 2) :
    a6 a b c d e f 1 = b := by rfl
@[simp] private theorem a6_at2 (a b c d e f : Fin 2) :
    a6 a b c d e f 2 = c := by rfl
@[simp] private theorem a6_at3 (a b c d e f : Fin 2) :
    a6 a b c d e f 3 = d := by rfl
@[simp] private theorem a6_at4 (a b c d e f : Fin 2) :
    a6 a b c d e f 4 = e := by rfl
@[simp] private theorem a6_at5 (a b c d e f : Fin 2) :
    a6 a b c d e f 5 = f := by rfl

@[simp] private theorem update_a6_0 (a b c d e f u : Fin 2) :
    Function.update (a6 a b c d e f) (0 : Fin 6) u =
      a6 u b c d e f := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem update_a6_1 (a b c d e f u : Fin 2) :
    Function.update (a6 a b c d e f) (1 : Fin 6) u =
      a6 a u c d e f := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem update_a6_2 (a b c d e f u : Fin 2) :
    Function.update (a6 a b c d e f) (2 : Fin 6) u =
      a6 a b u d e f := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem update_a6_3 (a b c d e f u : Fin 2) :
    Function.update (a6 a b c d e f) (3 : Fin 6) u =
      a6 a b c u e f := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem update_a6_4 (a b c d e f u : Fin 2) :
    Function.update (a6 a b c d e f) (4 : Fin 6) u =
      a6 a b c d u f := by
  funext i; fin_cases i <;> rfl
@[simp] private theorem update_a6_5 (a b c d e f u : Fin 2) :
    Function.update (a6 a b c d e f) (5 : Fin 6) u =
      a6 a b c d e u := by
  funext i; fin_cases i <;> rfl

private def dualCoordinate6 : Fin 6 → Fin 6 := ![0, 1, 2, 2, 4, 5]

private def dualUpper6 : Fin 6 → Fin 6 → Fin 2 :=
  ![gammaFiveSelectedMax, e61, e62, e62, w0110, gammaFiveSelectedMin]

private def dualAnchor6 : Fin 6 → Fin 6 → Fin 2 :=
  ![e62, w0110, e63, w010110, e60, w010110]

private noncomputable def dualAlpha6 : Fin 6 → ℝ :=
  ![(1 / 2 : ℝ), 1 / 2, 1, 3 / 2, -(1 / 2), -1]

private def dualConstraint6 : Fin 7 → CanonicalConstraintAtom 5 (Fin 2) :=
  ![.competitorMin z6,
    .competitorMax w011110,
    .competitorMax w101000,
    .topC 1 5,
    .topC 2 0,
    .topC 2 4,
    .topC 3 5]

private noncomputable def dualBeta6 : Fin 7 → ℝ :=
  ![(1 : ℝ), 3 / 2, 1 / 2, 1 / 2, 1, 1, 1 / 2]

private theorem update_z6_0_zero :
    Function.update z6 (0 : Fin 6) (0 : Fin 2) = z6 := by
  funext i; fin_cases i <;> rfl

private theorem update_z6_0_one :
    Function.update z6 (0 : Fin 6) (1 : Fin 2) = e60 := by
  funext i; fin_cases i <;> rfl

private theorem update_z6_1_zero :
    Function.update z6 (1 : Fin 6) (0 : Fin 2) = z6 := by
  funext i; fin_cases i <;> rfl

private theorem update_z6_1_one :
    Function.update z6 (1 : Fin 6) (1 : Fin 2) = e61 := by
  funext i; fin_cases i <;> rfl

private theorem update_z6_2_zero :
    Function.update z6 (2 : Fin 6) (0 : Fin 2) = z6 := by
  funext i; fin_cases i <;> rfl

private theorem update_z6_2_one :
    Function.update z6 (2 : Fin 6) (1 : Fin 2) = e62 := by
  funext i; fin_cases i <;> rfl

private theorem update_z6_3_zero :
    Function.update z6 (3 : Fin 6) (0 : Fin 2) = z6 := by
  funext i; fin_cases i <;> rfl

private theorem update_z6_3_one :
    Function.update z6 (3 : Fin 6) (1 : Fin 2) = e63 := by
  funext i; fin_cases i <;> rfl

private theorem update_z6_4_zero :
    Function.update z6 (4 : Fin 6) (0 : Fin 2) = z6 := by
  funext i; fin_cases i <;> rfl

private theorem update_z6_4_one :
    Function.update z6 (4 : Fin 6) (1 : Fin 2) = e64 := by
  funext i; fin_cases i <;> rfl

private theorem update_z6_5_zero :
    Function.update z6 (5 : Fin 6) (0 : Fin 2) = z6 := by
  funext i; fin_cases i <;> rfl

private theorem update_selectedMax_0_zero :
    Function.update gammaFiveSelectedMax (0 : Fin 6) (0 : Fin 2) = e64 := by
  funext i; fin_cases i <;> rfl

private theorem update_e62_0_one :
    Function.update e62 (0 : Fin 6) (1 : Fin 2) = w101000 := by
  funext i; fin_cases i <;> rfl

private theorem update_e61_1_zero :
    Function.update e61 (1 : Fin 6) (0 : Fin 2) = z6 := by
  funext i; fin_cases i <;> rfl

private theorem update_w0110_1_one :
    Function.update w0110 (1 : Fin 6) (1 : Fin 2) = w010110 := by
  funext i; fin_cases i <;> rfl

private theorem update_e62_2_zero :
    Function.update e62 (2 : Fin 6) (0 : Fin 2) = z6 := by
  funext i; fin_cases i <;> rfl

private theorem update_e63_2_one :
    Function.update e63 (2 : Fin 6) (1 : Fin 2) = w001100 := by
  funext i; fin_cases i <;> rfl

private theorem update_w010110_2_one :
    Function.update w010110 (2 : Fin 6) (1 : Fin 2) = w011110 := by
  funext i; fin_cases i <;> rfl

private theorem update_w0110_4_zero :
    Function.update w0110 (4 : Fin 6) (0 : Fin 2) = e63 := by
  funext i; fin_cases i <;> rfl

private theorem update_e60_4_one :
    Function.update e60 (4 : Fin 6) (1 : Fin 2) = gammaFiveSelectedMax := by
  funext i; fin_cases i <;> rfl

private theorem update_selectedMin_5_zero :
    Function.update gammaFiveSelectedMin (5 : Fin 6) (0 : Fin 2) = w001100 := by
  funext i; fin_cases i <;> rfl

private theorem update_w010110_5_one :
    Function.update w010110 (5 : Fin 6) (1 : Fin 2) =
      gammaFiveCompetitorMax := by
  funext i; fin_cases i <;> rfl

/-- The exact six-cycle, seven-active-inequality dual certificate recovered
from the rational LP solution. -/
noncomputable def gammaFiveWeightedCertificate :
    CanonicalUniformDecisionCertificate gammaFiveCell (Fin 6) (Fin 7) where
  coordinate := dualCoordinate6
  upperWorld := dualUpper6
  anchorWorld := dualAnchor6
  alpha := dualAlpha6
  constraintAtom := dualConstraint6
  beta := dualBeta6
  beta_nonnegative := by
    intro j
    fin_cases j <;> norm_num [dualBeta6]
  functional_identity := by
    intro F
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp [decisionLinearFunctional, gammaFiveCell, dualCoordinate6,
      dualUpper6, dualAnchor6, dualAlpha6, dualConstraint6, dualBeta6,
      canonicalConstraintValue, responseWitnessSpan, retainedResidual,
      gammaFiveSelected, gammaFiveCompetitor, gammaFiveSelectedMax,
      gammaFiveSelectedMin, gammaFiveCompetitorMax, gammaFiveCompetitorMin,
      gammaFiveResponseMax, gammaFiveResponseMin, w0110, w010110,
      w001100, w011110, w101000, pointMass6_response, cycleFunctional,
      update_z6_0_zero, update_z6_0_one, update_z6_1_zero,
      update_z6_1_one, update_z6_2_zero, update_z6_2_one,
      update_z6_3_zero, update_z6_3_one, update_z6_4_zero,
      update_z6_4_one, update_z6_5_zero, update_selectedMax_0_zero,
      update_e62_0_one, update_e61_1_zero, update_w0110_1_one,
      update_e62_2_zero, update_e63_2_one, update_w010110_2_one,
      update_w0110_4_zero, update_e60_4_one, update_selectedMin_5_zero,
      update_w010110_5_one, z6, e60, e61, e62, e63, e64, e65]
    ring

@[simp] theorem gammaFiveWeightedCertificate_mass :
    gammaFiveWeightedCertificate.mass = 5 := by
  norm_num [gammaFiveWeightedCertificate,
    CanonicalUniformDecisionCertificate.mass, dualAlpha6,
    Fin.sum_univ_succ]

/-- The weighted LP certificate supplies the matching uniform upper bound for
every numerical world inside this same active cell. -/
theorem gammaFiveCell_decisionInteraction_atMost_five :
    DecisionInteractionConstantAtMost gammaFiveCell 5 := by
  intro F hCell hUnit
  have h := canonicalUniformDecisionCertificate_sound gammaFiveCell
    gammaFiveWeightedCertificate F 1 (by norm_num) hCell hUnit
  simpa using h

/-- Together with the exact primal saturation witness, no smaller uniform
constant can hold on this cell. -/
theorem gammaFiveCell_exact_uniform_constant :
    DecisionInteractionConstantAtMost gammaFiveCell 5 ∧
      ∀ c : ℝ, c < 5 → ¬ DecisionInteractionConstantAtMost gammaFiveCell c := by
  exact ⟨gammaFiveCell_decisionInteraction_atMost_five,
    fun c hc ↦ gammaFiveCell_no_constant_below_five hc⟩

/-- Finite evidence for the observed `d ↦ d+1` increment: the certified mass
grows from three in the Fin-4 canonical cell to five in this Fin-6 cell.
This is a comparison theorem, not a general induction claim. -/
theorem fin4_to_fin6_mass_increment_two :
    gammaFiveWeightedCertificate.mass = canonicalCertificate4.mass + 2 := by
  rw [gammaFiveWeightedCertificate_mass, canonicalCertificate4_mass]
  norm_num

end CIGAMF.P13.D6Fin6WeightedDualCertificate
