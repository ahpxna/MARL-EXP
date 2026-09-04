import Mathlib
import «LeanD6PAECExistence»
import «LeanD6CostAwarePAECCompletionV1»

/-!
# Actual PAEC-to-cost-aware-certificate adapter

`LeanD6CostAwarePAECCompletionV1` proves robust interval evaluation for an
abstract linear certificate.  This file connects that API to the actual D6
object: a `HasPAECForPair` witness whose atoms are
`cycleFunctional i x c F`.

The result is deliberately conditional on the supplied PAEC witness.  It does
not assert the open `EveryTopCPairHasPAEC` existence theorem.
-/

namespace CIGAMF.P13.D6PAECCostAwareAdapter

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6PAECExistence
open CIGAMF.P13.D6CostAwarePAECCompletion

variable {U : Type*} [Fintype U] [Nonempty U]

noncomputable def PAECDecisionGap {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1))) : ℝ :=
  productCompressionLoss F (productResponse q F) selected -
    productCompressionLoss F (productResponse q F) competitor

abbrev PAECAtomValue {n r : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin r → Fin (n + 1))
    (x c : Fin r → Fin (n + 1) → U) : Fin r → ℝ :=
  fun a ↦ cycleFunctional (i a) (x a) (c a) F

/-- A concrete PAEC tuple is exactly a `ValidCertificate` whose atom values
are D6 cycle functionals. -/
noncomputable def paecWitness_to_validCertificate {n r : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (i : Fin r → Fin (n + 1))
    (x c : Fin r → Fin (n + 1) → U)
    (alpha : Fin r → ℝ) (correction : ℝ)
    (hCorrection : correction ≤ 0)
    (hCertificate :
      2 * PAECDecisionGap q F selected competitor ≤
        (∑ a, alpha a * PAECAtomValue F i x c a) + correction) :
    ValidCertificate (Fin r) (PAECAtomValue F i x c)
      (PAECDecisionGap q F selected competitor) := by
  exact
    { alpha := alpha
      correction := correction
      correction_nonpos := hCorrection
      sound := hCertificate }

/-- `HasPAECForPair` yields an actual D6 certificate accepted by the
cost-aware interval API, retaining the PAEC mass budget. -/
theorem hasPAEC_to_validCertificate {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (hPAEC : HasPAECForPair q F selected competitor) :
    ∃ (r : ℕ) (i : Fin r → Fin (n + 1))
      (x c : Fin r → Fin (n + 1) → U)
      (C : ValidCertificate (Fin r) (PAECAtomValue F i x c)
        (PAECDecisionGap q F selected competitor)),
      (∑ a, |C.alpha a|) ≤ (n : ℝ) := by
  rcases hPAEC with ⟨r, i, x, c, alpha, correction,
    hCorrection, hCertificate, hMass⟩
  refine ⟨r, i, x, c,
    paecWitness_to_validCertificate q F selected competitor i x c alpha
      correction hCorrection hCertificate, ?_⟩
  simpa [paecWitness_to_validCertificate] using hMass

/-- Actual specialization of D6-B1: intervals covering the measured D6 cycle
atoms safely upper-bound the selected-versus-competitor compression gap. -/
theorem hasPAEC_measured_cycle_intervals_sound {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (hPAEC : HasPAECForPair q F selected competitor) :
    ∃ (r : ℕ) (i : Fin r → Fin (n + 1))
      (x c : Fin r → Fin (n + 1) → U)
      (C : ValidCertificate (Fin r) (PAECAtomValue F i x c)
        (PAECDecisionGap q F selected competitor)),
      (∑ a, |C.alpha a|) ≤ (n : ℝ) ∧
      ∀ I : AtomIntervals (Fin r), Covers I (PAECAtomValue F i x c) →
        PAECDecisionGap q F selected competitor ≤ robustBound C I := by
  rcases hasPAEC_to_validCertificate q F selected competitor hPAEC with
    ⟨r, i, x, c, C, hMass⟩
  refine ⟨r, i, x, c, C, hMass, ?_⟩
  intro I hCovers
  exact D6_B1_certificate_specific_robust_bound
    (PAECAtomValue F i x c) (PAECDecisionGap q F selected competitor)
    C I hCovers

/-- If the actual PAEC cycle intervals certify a tolerance, the corresponding
selected-versus-competitor D6 gap is at most that tolerance. -/
theorem hasPAEC_cycle_interval_stop_safe {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (hPAEC : HasPAECForPair q F selected competitor) :
    ∃ (r : ℕ) (i : Fin r → Fin (n + 1))
      (x c : Fin r → Fin (n + 1) → U)
      (C : ValidCertificate (Fin r) (PAECAtomValue F i x c)
        (PAECDecisionGap q F selected competitor)),
      (∑ a, |C.alpha a|) ≤ (n : ℝ) ∧
      ∀ (I : AtomIntervals (Fin r)) (eps : ℝ),
        Covers I (PAECAtomValue F i x c) → robustBound C I ≤ eps →
          PAECDecisionGap q F selected competitor ≤ eps := by
  rcases hasPAEC_to_validCertificate q F selected competitor hPAEC with
    ⟨r, i, x, c, C, hMass⟩
  refine ⟨r, i, x, c, C, hMass, ?_⟩
  intro I eps hCovers hStop
  exact le_trans
    (D6_B1_certificate_specific_robust_bound
      (PAECAtomValue F i x c) (PAECDecisionGap q F selected competitor)
      C I hCovers) hStop

end CIGAMF.P13.D6PAECCostAwareAdapter
