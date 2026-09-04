import Mathlib
import «LeanD6PAECExistence»

/-!
# PAEC atomic/filling mass

This module gives the proposed theorem language for D6 certificates.  The
atomic mass is the infimum of the `ℓ₁` masses of all valid PAEC fillings of a
fixed selected-versus-competitor decision boundary.  It does not assert the
still-open theorem that every Top-C pair has such a filling.
-/

namespace CIGAMF.P13.D6PAECAtomicNorm

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6PAECExistence

variable {U : Type*} [Fintype U] [Nonempty U]

def HasPAECWithMass {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1))) (mass : ℝ) : Prop :=
  ∃ r : ℕ,
    ∃ i : Fin r → Fin (n + 1),
    ∃ x c : Fin r → Fin (n + 1) → U,
    ∃ alpha : Fin r → ℝ,
    ∃ correction : ℝ,
      correction ≤ 0 ∧
      2 * (productCompressionLoss F (productResponse q F) selected -
          productCompressionLoss F (productResponse q F) competitor) ≤
        (∑ a, alpha a * cycleFunctional (i a) (x a) (c a) F) +
          correction ∧
      (∑ a, |alpha a|) ≤ mass

noncomputable def paecAtomicMass {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1))) : ℝ :=
  sInf {mass : ℝ | HasPAECWithMass q F selected competitor mass}

noncomputable def paecGamma {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1))) : ℝ :=
  paecAtomicMass q F selected competitor / 2

theorem paec_mass_nonnegative {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    {mass : ℝ} (h : HasPAECWithMass q F selected competitor mass) :
    0 ≤ mass := by
  rcases h with ⟨r, i, x, c, alpha, correction, hc, hs, hm⟩
  exact le_trans (Finset.sum_nonneg fun a ha ↦ abs_nonneg (alpha a)) hm

theorem hasPAEC_implies_mass_feasible {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (h : HasPAECForPair q F selected competitor) :
    HasPAECWithMass q F selected competitor (n : ℝ) := by
  exact h

theorem pair_bound_of_PAECWithMass {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (delta mass : ℝ) (hdeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ i x c, |mixedDifference F i x c| ≤ delta)
    (hPAEC : HasPAECWithMass q F selected competitor mass) :
    productCompressionLoss F (productResponse q F) selected -
        productCompressionLoss F (productResponse q F) competitor ≤
      mass * delta / 2 := by
  rcases hPAEC with ⟨r, i, x, c, alpha, correction,
    hCorrection, hCertificate, hMass⟩
  have hCycle := finite_cycle_combination_bound F delta i x c alpha
    (fun a ↦ hdelta (i a) (x a) (c a))
  have hScale : delta * (∑ a, |alpha a|) ≤ delta * mass :=
    mul_le_mul_of_nonneg_left hMass hdeltaNonneg
  have hSigned :
      (∑ a, alpha a * cycleFunctional (i a) (x a) (c a) F) ≤
        delta * mass := by
    calc
      _ ≤ |∑ a, alpha a * cycleFunctional (i a) (x a) (c a) F| :=
        le_abs_self _
      _ ≤ delta * (∑ a, |alpha a|) := hCycle
      _ ≤ delta * mass := hScale
  nlinarith

theorem paecAtomicMass_nonnegative {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (hNonempty : ∃ mass, HasPAECWithMass q F selected competitor mass) :
    0 ≤ paecAtomicMass q F selected competitor := by
  unfold paecAtomicMass
  apply le_csInf
  · exact hNonempty
  · intro mass hmass
    exact paec_mass_nonnegative q F selected competitor hmass

theorem paecAtomicMass_le_of_feasible {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    {mass : ℝ} (h : HasPAECWithMass q F selected competitor mass) :
    paecAtomicMass q F selected competitor ≤ mass := by
  unfold paecAtomicMass
  exact csInf_le
    ⟨0, by
      intro y hy
      exact paec_mass_nonnegative q F selected competitor hy⟩ h

theorem hasPAEC_atomic_mass_le_dimension {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (h : HasPAECForPair q F selected competitor) :
    paecAtomicMass q F selected competitor ≤ (n : ℝ) :=
  paecAtomicMass_le_of_feasible q F selected competitor
    (hasPAEC_implies_mass_feasible q F selected competitor h)

/- The infimum itself is a sound filling norm.  Attainment is not assumed. -/
theorem pair_bound_by_paecGamma {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (delta : ℝ) (hdeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ i x c, |mixedDifference F i x c| ≤ delta)
    (hNonempty : ∃ mass, HasPAECWithMass q F selected competitor mass) :
    productCompressionLoss F (productResponse q F) selected -
        productCompressionLoss F (productResponse q F) competitor ≤
      paecGamma q F selected competitor * delta := by
  by_cases hzero : delta = 0
  · subst delta
    rcases hNonempty with ⟨mass, hmass⟩
    have h := pair_bound_of_PAECWithMass q F selected competitor 0 mass
      (by norm_num) hdelta hmass
    simpa [paecGamma] using h
  have hdeltaPos : 0 < delta := lt_of_le_of_ne hdeltaNonneg (Ne.symm hzero)
  let D := productCompressionLoss F (productResponse q F) selected -
    productCompressionLoss F (productResponse q F) competitor
  have hLower : 2 * D / delta ≤ paecAtomicMass q F selected competitor := by
    unfold paecAtomicMass
    apply le_csInf
    · exact hNonempty
    · intro mass hmass
      have hb := pair_bound_of_PAECWithMass q F selected competitor delta mass
        (le_of_lt hdeltaPos) hdelta hmass
      dsimp [D]
      apply (div_le_iff₀ hdeltaPos).2
      nlinarith
  unfold paecGamma
  have hMul : 2 * D ≤ paecAtomicMass q F selected competitor * delta :=
    (div_le_iff₀ hdeltaPos).mp hLower
  dsimp [D] at hMul ⊢
  calc
    _ ≤ (paecAtomicMass q F selected competitor * delta) / 2 := by
      linarith
    _ = paecAtomicMass q F selected competitor / 2 * delta := by ring

end CIGAMF.P13.D6PAECAtomicNorm
