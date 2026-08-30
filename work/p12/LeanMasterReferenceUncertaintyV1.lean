import Mathlib
import «LeanReferenceKernelV4»
import «LeanPairwiseMasterV4»

/-! Reference-kernel uncertainty for the active MASTER chain.

The error composition below is deliberately typed by a single terminal score
`C`; it is not a license to add bounds for different scientific estimands. -/

namespace CIGAMF.V7.MasterReferenceUncertainty

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.JointKernel
open CIGAMF.V4.Pairwise

variable {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

def RowwiseTVBound (κ κhat : A → B → ℝ) (eps : ℝ) : Prop :=
  ∀ a, tv (κ a) (κhat a) ≤ eps

theorem RU1_expectation_reference_error
    (κ κhat : A → B → ℝ) (hκ : Valid κ) (hκhat : Valid κhat)
    (H : B → ℝ) (eps : ℝ) (hTV : RowwiseTVBound κ κhat eps) (a : A) :
    |expectation κ H a - expectation κhat H a| ≤ osc H * eps := by
  have h := expectation_diff_le_tv_osc (κ a) (κhat a) H
    (hκ.2 a) (hκhat.2 a)
  have ht := hTV a
  have hosc : 0 ≤ osc H := osc_nonneg H
  calc
    |expectation κ H a - expectation κhat H a| ≤
        tv (κ a) (κhat a) * osc H := by
          simpa [expectation, mul_comm] using h
    _ ≤ eps * osc H := mul_le_mul_of_nonneg_right ht hosc
    _ = osc H * eps := by ring

theorem osc_diff_le_two_of_pointwise
    (f g : A → ℝ) (b : ℝ) (h : ∀ a, |f a - g a| ≤ b) :
    |osc f - osc g| ≤ 2 * b := by
  have hdev : osc (fun a => f a - g a) ≤ 2 * b := by
    have hmax : maxVal (fun a => f a - g a) ≤ b := by
      apply maxVal_le
      intro a
      exact (abs_le.mp (h a)).2
    have hmin : -b ≤ minVal (fun a => f a - g a) := by
      apply le_minVal
      intro a
      exact (abs_le.mp (h a)).1
    simp only [osc]
    linarith
  have hadd := osc_add_deviation g (fun a => f a - g a)
  have heq : (fun a => g a + (f a - g a)) = f := by
    funext a
    ring
  rw [heq] at hadd
  exact le_trans (by simpa [abs_sub_comm] using hadd) hdev

theorem RU2_chi_reference_error
    (κ κhat : A → B → ℝ) (hκ : Valid κ) (hκhat : Valid κhat)
    (H : B → ℝ) (eps : ℝ) (hTV : RowwiseTVBound κ κhat eps) :
    |osc (fun a => expectation κ H a) -
      osc (fun a => expectation κhat H a)| ≤ 2 * osc H * eps := by
  apply le_trans (osc_diff_le_two_of_pointwise
    (fun a => expectation κ H a) (fun a => expectation κhat H a)
    (osc H * eps) (fun a => RU1_expectation_reference_error
      κ κhat hκ hκhat H eps hTV a))
  simpa [mul_assoc, mul_comm, mul_left_comm]

/- The factor two in RU2 is attained: the baseline kernel has identical
uniform rows, while the perturbed kernel moves the two rows in opposite
directions. -/
noncomputable def uniformKernel22 (_a _b : Fin 2) : ℝ := 1 / 2

def separatedKernel22 (a b : Fin 2) : ℝ :=
  if a = b then 1 else 0

def binaryH (b : Fin 2) : ℝ := if b = 0 then 0 else 1

theorem uniformKernel22_valid : Valid uniformKernel22 := by
  constructor
  · intro a b
    norm_num [uniformKernel22]
  · intro a
    fin_cases a <;> norm_num [uniformKernel22, Fin.sum_univ_two]

theorem separatedKernel22_valid : Valid separatedKernel22 := by
  constructor
  · intro a b
    unfold separatedKernel22
    split_ifs <;> norm_num
  · intro a
    fin_cases a <;> norm_num [separatedKernel22, Fin.sum_univ_two]

theorem RU2_factor_two_sharp_witness :
    RowwiseTVBound uniformKernel22 separatedKernel22 (1 / 2) ∧
    |osc (fun a => expectation uniformKernel22 binaryH a) -
      osc (fun a => expectation separatedKernel22 binaryH a)| =
        2 * osc binaryH * (1 / 2) := by
  constructor
  · intro a
    fin_cases a <;>
      norm_num [tv, uniformKernel22, separatedKernel22, Fin.sum_univ_two]
  · have huFun : (fun a => expectation uniformKernel22 binaryH a) =
        (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
      funext a
      fin_cases a <;>
        norm_num [expectation, uniformKernel22, binaryH, Fin.sum_univ_two]
    have hsFun : (fun a => expectation separatedKernel22 binaryH a) = binaryH := by
      funext a
      fin_cases a <;>
        norm_num [expectation, separatedKernel22, binaryH, Fin.sum_univ_two]
    have hconst : osc (fun _ : Fin 2 => (1 / 2 : ℝ)) = 0 := by
      have hmax : maxVal (fun _ : Fin 2 => (1 / 2 : ℝ)) = 1 / 2 := by
        apply le_antisymm
        · exact maxVal_le _ (fun _ => le_rfl)
        · exact le_maxVal (fun _ : Fin 2 => (1 / 2 : ℝ)) (0 : Fin 2)
      have hmin : minVal (fun _ : Fin 2 => (1 / 2 : ℝ)) = 1 / 2 := by
        apply le_antisymm
        · exact minVal_le (fun _ : Fin 2 => (1 / 2 : ℝ)) (0 : Fin 2)
        · exact le_minVal _ (fun _ => le_rfl)
      unfold osc
      rw [hmax, hmin]
      ring
    have hbinary : osc binaryH = 1 := by
      have hmax : maxVal binaryH = 1 := by
        apply le_antisymm
        · apply maxVal_le
          intro a
          fin_cases a <;> norm_num [binaryH]
        · simpa [binaryH] using le_maxVal binaryH (1 : Fin 2)
      have hmin : minVal binaryH = 0 := by
        apply le_antisymm
        · simpa [binaryH] using minVal_le binaryH (0 : Fin 2)
        · apply le_minVal
          intro a
          fin_cases a <;> norm_num [binaryH]
      simp [osc, hmax, hmin]
    rw [huFun, hsFun, hconst, hbinary]
    norm_num

theorem RU3_primitive_score_reference_interval
    (primitive : A → ℝ) (κ κhat : A → B → ℝ)
    (hκ : Valid κ) (hκhat : Valid κhat)
    (H : B → ℝ) (eps : ℝ) (hTV : RowwiseTVBound κ κhat eps) :
    |osc (fun a => primitive a + expectation κ H a) - osc primitive| ≤
      osc (fun a => expectation κhat H a) + 2 * osc H * eps := by
  have hiso := osc_add_deviation primitive (fun a => expectation κ H a)
  have href := RU2_chi_reference_error κ κhat hκ hκhat H eps hTV
  have hchi : osc (fun a => expectation κ H a) ≤
      osc (fun a => expectation κhat H a) + 2 * osc H * eps := by
    linarith [abs_le.mp href]
  exact le_trans hiso hchi

/- Four explicitly named stages, all ending at the same terminal score `C`.
This makes the semantic condition visible in the theorem type. -/
structure SameTargetScoreChain (ι : Type*) where
  target : ι → ℝ
  afterModel : ι → ℝ
  afterSupport : ι → ℝ
  afterReference : ι → ℝ
  estimate : ι → ℝ

def totalError (eStat eRef eSupport eModel : ι → ℝ) (j : ι) : ℝ :=
  eStat j + eRef j + eSupport j + eModel j

theorem RU4_same_target_error_composition
    {ι : Type*} (chain : SameTargetScoreChain ι)
    (eStat eRef eSupport eModel : ι → ℝ)
    (hStat : ∀ j, |chain.estimate j - chain.afterReference j| ≤ eStat j)
    (hRef : ∀ j, |chain.afterReference j - chain.afterSupport j| ≤ eRef j)
    (hSupport : ∀ j, |chain.afterSupport j - chain.afterModel j| ≤ eSupport j)
    (hModel : ∀ j, |chain.afterModel j - chain.target j| ≤ eModel j) :
    scoreCovered chain.target chain.estimate
      (totalError eStat eRef eSupport eModel) := by
  intro j
  unfold totalError
  calc
    |chain.estimate j - chain.target j| ≤
        |chain.estimate j - chain.afterReference j| +
        |chain.afterReference j - chain.afterSupport j| +
        |chain.afterSupport j - chain.afterModel j| +
        |chain.afterModel j - chain.target j| := by
          linarith [abs_sub_le (chain.estimate j) (chain.afterReference j) (chain.target j),
            abs_sub_le (chain.afterReference j) (chain.afterSupport j) (chain.target j),
            abs_sub_le (chain.afterSupport j) (chain.afterModel j) (chain.target j)]
    _ ≤ eStat j + eRef j + eSupport j + eModel j := by
          exact add_le_add (add_le_add (add_le_add (hStat j) (hRef j))
            (hSupport j)) (hModel j)

theorem RU5_composed_reference_uncertainty_MASTER
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι]
    (f : ι → Ω → ℝ) (chain : SameTargetScoreChain ι)
    (eStat eRef eSupport eModel : ι → ℝ) (L : Finset ι → ℝ)
    (trueTop selected optimum : Finset ι) (k : ℕ) (eta : ℝ)
    (hTarget : chain.target = componentSpan f)
    (hStat : ∀ j, |chain.estimate j - chain.afterReference j| ≤ eStat j)
    (hRef : ∀ j, |chain.afterReference j - chain.afterSupport j| ≤ eRef j)
    (hSupport : ∀ j, |chain.afterSupport j - chain.afterModel j| ≤ eSupport j)
    (hModel : ∀ j, |chain.afterModel j - chain.target j| ≤ eModel j)
    (hTop : IsTopKByScore (componentSpan f) trueTop k)
    (hSelectedCard : selected.card = k) (hOptCard : optimum.card = k)
    (hDownstreamUniform : ∀ S : Finset ι, S.card = k →
      |L S - selectedRadius f S| ≤ eta) :
    L selected - L optimum ≤
      operationalGamma chain.estimate
        (totalError eStat eRef eSupport eModel)
        (canonicalTopK (upperScore chain.estimate
          (totalError eStat eRef eSupport eModel)) k) selected +
        zetaDefFinite f k / 2 + 2 * eta := by
  have hcover := RU4_same_target_error_composition chain
    eStat eRef eSupport eModel hStat hRef hSupport hModel
  rw [hTarget] at hcover
  exact FULLY_INSTANTIATED_OPERATIONAL_MASTER f chain.estimate
    (totalError eStat eRef eSupport eModel) L trueTop selected optimum k eta
    hcover hTop hSelectedCard hOptCard hDownstreamUniform

end CIGAMF.V7.MasterReferenceUncertainty
