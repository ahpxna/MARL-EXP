import Mathlib
import «LeanFunctionalBoundaryV4»

/-! Algebraic covariance-design consequences.  No probabilistic covariance
identity is asserted; `quadraticVariance` is the deterministic quadratic form. -/

namespace CIGAMF.V7.FunctionalCovarianceDesign

open scoped BigOperators

def quadraticVariance {n : ℕ} (Sigma : Fin n → Fin n → ℝ)
    (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * Sigma i j * v j

def linearFunctional {n : ℕ} (v Q : Fin n → ℝ) : ℝ := ∑ i, v i * Q i

def unitContrast {n : ℕ} [DecidableEq (Fin n)]
    (aPlus aMinus : Fin n) (i : Fin n) : ℝ :=
  if i = aPlus then 1 else if i = aMinus then -1 else 0

theorem FCOV1_D_error_uses_w {n : ℕ} (w Q Qhat : Fin n → ℝ) :
    linearFunctional w Qhat - linearFunctional w Q =
      linearFunctional w (fun i => Qhat i - Q i) := by
  unfold linearFunctional
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem FCOV2_stable_extrema_C_uses_unit_contrast {n : ℕ}
    [DecidableEq (Fin n)] (Q Qhat : Fin n → ℝ) (aPlus aMinus : Fin n)
    (hne : aPlus ≠ aMinus) :
    (Qhat aPlus - Qhat aMinus) - (Q aPlus - Q aMinus) =
      linearFunctional (unitContrast aPlus aMinus) (fun i => Qhat i - Q i) := by
  classical
  unfold linearFunctional
  have hfun : (fun i => unitContrast aPlus aMinus i * (Qhat i - Q i)) =
      (fun i => (if i = aPlus then Qhat i - Q i else 0) +
        (if i = aMinus then -(Qhat i - Q i) else 0)) := by
    funext i
    by_cases hp : i = aPlus
    · subst i
      simp [unitContrast, hne]
    · by_cases hm : i = aMinus
      · subst i
        simp [unitContrast, hp]
      · simp [unitContrast, hp, hm]
  rw [hfun, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

def diagonalVariance {n : ℕ} (d v : Fin n → ℝ) : ℝ :=
  ∑ i, d i * (v i)^2

theorem FCOV3_diagonal_reduction {n : ℕ}
    (Sigma : Fin n → Fin n → ℝ) (d v : Fin n → ℝ)
    (hdiag : ∀ i, Sigma i i = d i)
    (hoff : ∀ i j, i ≠ j → Sigma i j = 0) :
    quadraticVariance Sigma v = diagonalVariance d v := by
  classical
  unfold quadraticVariance diagonalVariance
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · rw [hdiag]
    ring
  · intro j hj hne
    rw [hoff i j hne.symm]
    ring
  · simp

def IsPSD {n : ℕ} (Sigma : Fin n → Fin n → ℝ) : Prop :=
  ∀ v, 0 ≤ quadraticVariance Sigma v

noncomputable def SigmaA (i j : Fin 2) : ℝ :=
  if i = j then 1 else 9 / 10

noncomputable def SigmaB (i j : Fin 2) : ℝ :=
  if i = j then 3 / 5 else -(1 / 2)

def contrast2 (i : Fin 2) : ℝ := if i = 0 then 1 else -1

theorem SigmaA_psd : IsPSD SigmaA := by
  intro v
  have hid : quadraticVariance SigmaA v =
      (19 / 20 : ℝ) * (v 0 + v 1)^2 + (1 / 20 : ℝ) * (v 0 - v 1)^2 := by
    simp [quadraticVariance, SigmaA, Fin.sum_univ_two]
    ring
  rw [hid]
  positivity

theorem SigmaB_psd : IsPSD SigmaB := by
  intro v
  have hid : quadraticVariance SigmaB v =
      (1 / 20 : ℝ) * (v 0 + v 1)^2 + (11 / 20 : ℝ) * (v 0 - v 1)^2 := by
    simp [quadraticVariance, SigmaB, Fin.sum_univ_two]
    ring
  rw [hid]
  positivity

theorem FCOV_design_misranking_witness :
    IsPSD SigmaA ∧ IsPSD SigmaB ∧
    diagonalVariance (fun i => SigmaB i i) contrast2 <
      diagonalVariance (fun i => SigmaA i i) contrast2 ∧
    quadraticVariance SigmaA contrast2 < quadraticVariance SigmaB contrast2 := by
  refine ⟨SigmaA_psd, SigmaB_psd, ?_, ?_⟩
  · norm_num [diagonalVariance, SigmaA, SigmaB, contrast2, Fin.sum_univ_two]
  · norm_num [quadraticVariance, SigmaA, SigmaB, contrast2, Fin.sum_univ_two]

end CIGAMF.V7.FunctionalCovarianceDesign
