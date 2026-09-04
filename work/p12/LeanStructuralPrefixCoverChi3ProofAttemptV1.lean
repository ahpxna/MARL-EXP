import Mathlib
import «LeanStructuralPrefixCoverChi3WitnessV1»

/-!
# Exact `chi_prefix >= 3` proof attempt for the five-atom CIG support witness

This module contains only the finite proof work needed to promote the exact
search witness in `LeanStructuralPrefixCoverChi3WitnessV1`.  It does not alter
the generic prefix-cover API.
-/

namespace CIGAMF.P13.StructuralPrefixCoverChi3ProofAttempt

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.StructuralGeometryWitnesses
open CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralPrefixCoverWitnesses

/- Pointwise finite table, made explicit so every later radius calculation is
   auditable rather than delegated to an opaque reduction. -/
@[simp] private theorem chi3_0_0 : chi3F (0 : Fin 5) 0 = 0 := by rfl
@[simp] private theorem chi3_1_0 : chi3F (1 : Fin 5) 0 = 0 := by rfl
@[simp] private theorem chi3_2_0 : chi3F (2 : Fin 5) 0 = 0 := by rfl
@[simp] private theorem chi3_3_0 : chi3F (3 : Fin 5) 0 = 3 := by rfl
@[simp] private theorem chi3_4_0 : chi3F (4 : Fin 5) 0 = -3 := by rfl

@[simp] private theorem chi3_0_1 : chi3F (0 : Fin 5) 1 = 0 := by rfl
@[simp] private theorem chi3_1_1 : chi3F (1 : Fin 5) 1 = 0 := by rfl
@[simp] private theorem chi3_2_1 : chi3F (2 : Fin 5) 1 = 3 := by rfl
@[simp] private theorem chi3_3_1 : chi3F (3 : Fin 5) 1 = 0 := by rfl
@[simp] private theorem chi3_4_1 : chi3F (4 : Fin 5) 1 = 0 := by rfl

@[simp] private theorem chi3_0_2 : chi3F (0 : Fin 5) 2 = 0 := by rfl
@[simp] private theorem chi3_1_2 : chi3F (1 : Fin 5) 2 = -3 := by rfl
@[simp] private theorem chi3_2_2 : chi3F (2 : Fin 5) 2 = 0 := by rfl
@[simp] private theorem chi3_3_2 : chi3F (3 : Fin 5) 2 = 3 := by rfl
@[simp] private theorem chi3_4_2 : chi3F (4 : Fin 5) 2 = 0 := by rfl

@[simp] private theorem chi3_0_3 : chi3F (0 : Fin 5) 3 = -1 := by rfl
@[simp] private theorem chi3_1_3 : chi3F (1 : Fin 5) 3 = 0 := by rfl
@[simp] private theorem chi3_2_3 : chi3F (2 : Fin 5) 3 = 3 := by rfl
@[simp] private theorem chi3_3_3 : chi3F (3 : Fin 5) 3 = 0 := by rfl
@[simp] private theorem chi3_4_3 : chi3F (4 : Fin 5) 3 = 0 := by rfl

@[simp] private theorem chi3_0_4 : chi3F (0 : Fin 5) 4 = -1 := by rfl
@[simp] private theorem chi3_1_4 : chi3F (1 : Fin 5) 4 = -3 := by rfl
@[simp] private theorem chi3_2_4 : chi3F (2 : Fin 5) 4 = 0 := by rfl
@[simp] private theorem chi3_3_4 : chi3F (3 : Fin 5) 4 = 3 := by rfl
@[simp] private theorem chi3_4_4 : chi3F (4 : Fin 5) 4 = 0 := by rfl

@[simp] private theorem fin5_compl_0 :
    ({0} : Finset (Fin 5))ᶜ = {1, 2, 3, 4} := by decide
@[simp] private theorem fin5_compl_1 :
    ({1} : Finset (Fin 5))ᶜ = {0, 2, 3, 4} := by decide
@[simp] private theorem fin5_compl_2 :
    ({2} : Finset (Fin 5))ᶜ = {0, 1, 3, 4} := by decide
@[simp] private theorem fin5_compl_3 :
    ({3} : Finset (Fin 5))ᶜ = {0, 1, 2, 4} := by decide
@[simp] private theorem fin5_compl_4 :
    ({4} : Finset (Fin 5))ᶜ = {0, 1, 2, 3} := by decide

@[simp] private theorem pair_10 : ({1, 0} : Finset (Fin 5)) = {0, 1} := by decide
@[simp] private theorem pair_20 : ({2, 0} : Finset (Fin 5)) = {0, 2} := by decide
@[simp] private theorem pair_30 : ({3, 0} : Finset (Fin 5)) = {0, 3} := by decide
@[simp] private theorem pair_40 : ({4, 0} : Finset (Fin 5)) = {0, 4} := by decide
@[simp] private theorem pair_21 : ({2, 1} : Finset (Fin 5)) = {1, 2} := by decide
@[simp] private theorem pair_31 : ({3, 1} : Finset (Fin 5)) = {1, 3} := by decide
@[simp] private theorem pair_41 : ({4, 1} : Finset (Fin 5)) = {1, 4} := by decide
@[simp] private theorem pair_32 : ({3, 2} : Finset (Fin 5)) = {2, 3} := by decide
@[simp] private theorem pair_42 : ({4, 2} : Finset (Fin 5)) = {2, 4} := by decide
@[simp] private theorem pair_43 : ({4, 3} : Finset (Fin 5)) = {3, 4} := by decide
@[simp] private theorem erase_0134_1 :
    ({0, 1, 3, 4} : Finset (Fin 5)).erase 1 = {0, 3, 4} := by decide
@[simp] private theorem erase_0124_1 :
    ({0, 1, 2, 4} : Finset (Fin 5)).erase 1 = {0, 2, 4} := by decide
@[simp] private theorem erase_0123_1 :
    ({0, 1, 2, 3} : Finset (Fin 5)).erase 1 = {0, 2, 3} := by decide
@[simp] private theorem erase_0124_2 :
    ({0, 1, 2, 4} : Finset (Fin 5)).erase 2 = {0, 1, 4} := by decide
@[simp] private theorem erase_0123_2 :
    ({0, 1, 2, 3} : Finset (Fin 5)).erase 2 = {0, 1, 3} := by decide
@[simp] private theorem erase_0123_3 :
    ({0, 1, 2, 3} : Finset (Fin 5)).erase 3 = {0, 1, 2} := by decide

example : (∑ j ∈ ({1, 2, 3, 4} : Finset (Fin 5)), chi3F j 0) = 0 := by
  rw [Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_insert]
      · rw [Finset.sum_singleton]
        norm_num
      · decide
    · decide
  · decide

private theorem radius_02 :
    selectedRadius chi3F ({0, 2} : Finset (Fin 5)) = 0 := by
  calc
    _ = (0 - 0 : ℝ) / 2 := selectedRadius_from_extrema chi3F {0, 2} 0 0
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      0 0 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 0 := by norm_num

private theorem radius_01 :
    selectedRadius chi3F ({0, 1} : Finset (Fin 5)) = 3 / 2 := by
  calc
    _ = (3 - 0 : ℝ) / 2 := selectedRadius_from_extrema chi3F {0, 1} 3 0
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      1 0 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 / 2 := by norm_num

private theorem radius_compl_23 :
    selectedRadius chi3F (({2, 3} : Finset (Fin 5))ᶜ) = 0 := by
  calc
    _ = (3 - 3 : ℝ) / 2 := selectedRadius_from_extrema chi3F ({2, 3}ᶜ) 3 3
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      0 0 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 0 := by norm_num

private theorem radius_compl_01 :
    selectedRadius chi3F (({0, 1} : Finset (Fin 5))ᶜ) = 2 := by
  calc
    _ = (0 - (-4 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({0, 1}ᶜ) 0 (-4)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      0 4 (by simp [sumComponent, chi3F] <;> norm_num)
        (by simp [sumComponent, chi3F] <;> norm_num)
    _ = 2 := by norm_num

private theorem radius_compl_0 :
    selectedRadius chi3F (({0} : Finset (Fin 5))ᶜ) = 1 / 2 := by
  calc
    _ = (0 - (-1 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({0}ᶜ) 0 (-1)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      0 3 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 1 / 2 := by norm_num

private theorem radius_compl_1 :
    selectedRadius chi3F (({1} : Finset (Fin 5))ᶜ) = 3 / 2 := by
  calc
    _ = (0 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({1}ᶜ) 0 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      0 2 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 / 2 := by norm_num


private theorem radius_03 :
    selectedRadius chi3F ({0, 3} : Finset (Fin 5)) = 3 := by
  calc
    _ = (3 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema chi3F {0, 3} 3 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      1 0 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 := by norm_num

private theorem radius_04 :
    selectedRadius chi3F ({0, 4} : Finset (Fin 5)) = 3 / 2 := by
  calc
    _ = (3 - (0 : ℝ)) / 2 := selectedRadius_from_extrema chi3F {0, 4} 3 0
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      0 2 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 / 2 := by norm_num

private theorem radius_12 :
    selectedRadius chi3F ({1, 2} : Finset (Fin 5)) = 2 := by
  calc
    _ = (3 - (-1 : ℝ)) / 2 := selectedRadius_from_extrema chi3F {1, 2} 3 (-1)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      2 3 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 2 := by norm_num

private theorem radius_13 :
    selectedRadius chi3F ({1, 3} : Finset (Fin 5)) = 3 := by
  calc
    _ = (3 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema chi3F {1, 3} 3 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      1 0 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 := by norm_num

private theorem radius_14 :
    selectedRadius chi3F ({1, 4} : Finset (Fin 5)) = 1 / 2 := by
  calc
    _ = (3 - (2 : ℝ)) / 2 := selectedRadius_from_extrema chi3F {1, 4} 3 2
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      0 3 (by simp [sumComponent, chi3F] <;> norm_num)
        (by simp [sumComponent, chi3F] <;> norm_num)
    _ = 1 / 2 := by norm_num

private theorem radius_23 :
    selectedRadius chi3F ({2, 3} : Finset (Fin 5)) = 2 := by
  calc
    _ = (0 - (-4 : ℝ)) / 2 := selectedRadius_from_extrema chi3F {2, 3} 0 (-4)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      1 4 (by simp [sumComponent, chi3F] <;> norm_num)
        (by simp [sumComponent, chi3F] <;> norm_num)
    _ = 2 := by norm_num

private theorem radius_24 :
    selectedRadius chi3F ({2, 4} : Finset (Fin 5)) = 2 := by
  calc
    _ = (3 - (-1 : ℝ)) / 2 := selectedRadius_from_extrema chi3F {2, 4} 3 (-1)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      0 3 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 2 := by norm_num

private theorem radius_34 :
    selectedRadius chi3F ({3, 4} : Finset (Fin 5)) = 7 / 2 := by
  calc
    _ = (3 - (-4 : ℝ)) / 2 := selectedRadius_from_extrema chi3F {3, 4} 3 (-4)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      1 4 (by simp [sumComponent, chi3F] <;> norm_num)
        (by simp [sumComponent, chi3F] <;> norm_num)
    _ = 7 / 2 := by norm_num

private theorem radius_compl_02 :
    selectedRadius chi3F (({0, 2} : Finset (Fin 5))ᶜ) = 2 := by
  calc
    _ = (3 - (-1 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({0, 2}ᶜ) 3 (-1)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      1 4 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 2 := by norm_num

private theorem radius_compl_03 :
    selectedRadius chi3F (({0, 3} : Finset (Fin 5))ᶜ) = 2 := by
  calc
    _ = (3 - (-1 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({0, 3}ᶜ) 3 (-1)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      0 3 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 2 := by norm_num

private theorem radius_compl_04 :
    selectedRadius chi3F (({0, 4} : Finset (Fin 5))ᶜ) = 3 / 2 := by
  calc
    _ = (0 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({0, 4}ᶜ) 0 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      1 0 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 / 2 := by norm_num

private theorem radius_compl_12 :
    selectedRadius chi3F (({1, 2} : Finset (Fin 5))ᶜ) = 3 := by
  calc
    _ = (3 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({1, 2}ᶜ) 3 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      1 2 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 := by norm_num

private theorem radius_compl_13 :
    selectedRadius chi3F (({1, 3} : Finset (Fin 5))ᶜ) = 3 / 2 := by
  calc
    _ = (3 - (0 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({1, 3}ᶜ) 3 0
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      0 1 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 / 2 := by norm_num

private theorem radius_compl_14 :
    selectedRadius chi3F (({1, 4} : Finset (Fin 5))ᶜ) = 3 / 2 := by
  calc
    _ = (0 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({1, 4}ᶜ) 0 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      1 0 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 / 2 := by norm_num

private theorem radius_compl_24 :
    selectedRadius chi3F (({2, 4} : Finset (Fin 5))ᶜ) = 3 := by
  calc
    _ = (3 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({2, 4}ᶜ) 3 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      1 0 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 := by norm_num

private theorem radius_compl_34 :
    selectedRadius chi3F (({3, 4} : Finset (Fin 5))ᶜ) = 3 / 2 := by
  calc
    _ = (3 - (0 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({3, 4}ᶜ) 3 0
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      2 0 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 / 2 := by norm_num

private theorem radius_compl_2 :
    selectedRadius chi3F (({2} : Finset (Fin 5))ᶜ) = 3 / 2 := by
  calc
    _ = (3 - (0 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({2}ᶜ) 3 0
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      1 0 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 / 2 := by norm_num

private theorem radius_compl_3 :
    selectedRadius chi3F (({3} : Finset (Fin 5))ᶜ) = 3 / 2 := by
  calc
    _ = (3 - (0 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({3}ᶜ) 3 0
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      0 1 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 / 2 := by norm_num

private theorem radius_compl_4 :
    selectedRadius chi3F (({4} : Finset (Fin 5))ᶜ) = 3 / 2 := by
  calc
    _ = (0 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema chi3F ({4}ᶜ) 0 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, chi3F] <;> norm_num)
      1 0 (by simp [sumComponent, chi3F]) (by simp [sumComponent, chi3F])
    _ = 3 / 2 := by norm_num

/- Canonical names for the concrete three- and four-element sets produced by
   `fin_cases`.  Keeping these as aliases makes the uniqueness proof below a
   transparent finite table check rather than relying on complement
   normalization inside `simp`. -/
@[simp] private theorem radius_234 :
    selectedRadius chi3F ({2, 3, 4} : Finset (Fin 5)) = 2 := by
  rw [show ({2, 3, 4} : Finset (Fin 5)) = ({0, 1} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_01
@[simp] private theorem radius_134 :
    selectedRadius chi3F ({1, 3, 4} : Finset (Fin 5)) = 2 := by
  rw [show ({1, 3, 4} : Finset (Fin 5)) = ({0, 2} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_02
@[simp] private theorem radius_124 :
    selectedRadius chi3F ({1, 2, 4} : Finset (Fin 5)) = 2 := by
  rw [show ({1, 2, 4} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_03
@[simp] private theorem radius_123 :
    selectedRadius chi3F ({1, 2, 3} : Finset (Fin 5)) = 3 / 2 := by
  rw [show ({1, 2, 3} : Finset (Fin 5)) = ({0, 4} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_04
@[simp] private theorem radius_034 :
    selectedRadius chi3F ({0, 3, 4} : Finset (Fin 5)) = 3 := by
  rw [show ({0, 3, 4} : Finset (Fin 5)) = ({1, 2} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_12
@[simp] private theorem radius_024 :
    selectedRadius chi3F ({0, 2, 4} : Finset (Fin 5)) = 3 / 2 := by
  rw [show ({0, 2, 4} : Finset (Fin 5)) = ({1, 3} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_13
@[simp] private theorem radius_023 :
    selectedRadius chi3F ({0, 2, 3} : Finset (Fin 5)) = 3 / 2 := by
  rw [show ({0, 2, 3} : Finset (Fin 5)) = ({1, 4} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_14
@[simp] private theorem radius_014 :
    selectedRadius chi3F ({0, 1, 4} : Finset (Fin 5)) = 0 := by
  rw [show ({0, 1, 4} : Finset (Fin 5)) = ({2, 3} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_23
@[simp] private theorem radius_013 :
    selectedRadius chi3F ({0, 1, 3} : Finset (Fin 5)) = 3 := by
  rw [show ({0, 1, 3} : Finset (Fin 5)) = ({2, 4} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_24
@[simp] private theorem radius_012 :
    selectedRadius chi3F ({0, 1, 2} : Finset (Fin 5)) = 3 / 2 := by
  rw [show ({0, 1, 2} : Finset (Fin 5)) = ({3, 4} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_34

@[simp] private theorem radius_1234 :
    selectedRadius chi3F ({1, 2, 3, 4} : Finset (Fin 5)) = 1 / 2 := by
  rw [show ({1, 2, 3, 4} : Finset (Fin 5)) = ({0} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_0
@[simp] private theorem radius_0234 :
    selectedRadius chi3F ({0, 2, 3, 4} : Finset (Fin 5)) = 3 / 2 := by
  rw [show ({0, 2, 3, 4} : Finset (Fin 5)) = ({1} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_1
@[simp] private theorem radius_0134 :
    selectedRadius chi3F ({0, 1, 3, 4} : Finset (Fin 5)) = 3 / 2 := by
  rw [show ({0, 1, 3, 4} : Finset (Fin 5)) = ({2} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_2
@[simp] private theorem radius_0124 :
    selectedRadius chi3F ({0, 1, 2, 4} : Finset (Fin 5)) = 3 / 2 := by
  rw [show ({0, 1, 2, 4} : Finset (Fin 5)) = ({3} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_3
@[simp] private theorem radius_0123 :
    selectedRadius chi3F ({0, 1, 2, 3} : Finset (Fin 5)) = 3 / 2 := by
  rw [show ({0, 1, 2, 3} : Finset (Fin 5)) = ({4} : Finset (Fin 5))ᶜ by decide]
  exact radius_compl_4

private theorem chi3_unique_optimal_two
    (S : Finset (Fin 5))
    (hS : EpsilonOptimalAt (selectedRadius chi3F) 0 2 S) :
    S = ({0, 2} : Finset (Fin 5)) := by
  have hle := hS.2 ({0, 2} : Finset (Fin 5)) (by decide)
  rcases Finset.card_eq_two.mp hS.1 with ⟨a, b, hab, rfl⟩
  fin_cases a <;> fin_cases b <;>
    simp_all [radius_01, radius_02, radius_03, radius_04,
      radius_12, radius_13, radius_14, radius_23, radius_24, radius_34] <;>
    norm_num at hle

private theorem chi3_unique_optimal_three
    (S : Finset (Fin 5))
    (hS : EpsilonOptimalAt (selectedRadius chi3F) 0 3 S) :
    S = ({0, 1, 4} : Finset (Fin 5)) := by
  have hle := hS.2 ({0, 1, 4} : Finset (Fin 5)) (by decide)
  have hcompCard : Sᶜ.card = 2 := by
    simp [Finset.card_compl, hS.1]
  rcases Finset.card_eq_two.mp hcompCard with ⟨a, b, hab, hcomp⟩
  have hrepr : S = ({a, b} : Finset (Fin 5))ᶜ := by
    rw [← hcomp, compl_compl]
  rw [hrepr] at hle ⊢
  fin_cases a <;> fin_cases b <;>
    simp_all [radius_compl_01, radius_compl_02, radius_compl_03,
      radius_compl_04, radius_compl_12, radius_compl_13,
      radius_compl_14, radius_compl_23, radius_compl_24,
      radius_compl_34, radius_234, radius_134, radius_124,
      radius_123, radius_034, radius_024, radius_023, radius_014,
      radius_013, radius_012] <;> norm_num at hle

private theorem chi3_unique_optimal_four
    (S : Finset (Fin 5))
    (hS : EpsilonOptimalAt (selectedRadius chi3F) 0 4 S) :
    S = ({1, 2, 3, 4} : Finset (Fin 5)) := by
  have hle := hS.2 ({1, 2, 3, 4} : Finset (Fin 5)) (by decide)
  have hcompCard : Sᶜ.card = 1 := by
    simp [Finset.card_compl, hS.1]
  rcases Finset.card_eq_one.mp hcompCard with ⟨a, hcomp⟩
  have hrepr : S = ({a} : Finset (Fin 5))ᶜ := by
    rw [← hcomp, compl_compl]
  rw [hrepr] at hle ⊢
  fin_cases a <;> simp_all [radius_compl_0, radius_compl_1,
    radius_compl_2, radius_compl_3, radius_compl_4] <;>
    norm_num at hle

private theorem prefixSet_mono
    (ranking : List (Fin 5)) {k l : ℕ} (hkl : k ≤ l) :
    prefixSet ranking k ⊆ prefixSet ranking l := by
  intro x hx
  have hp : ranking.take k <+: ranking.take l :=
    List.take_prefix_take_left hkl
  have hxList : x ∈ ranking.take k := by
    simpa [prefixSet] using hx
  have : x ∈ ranking.take l := hp.subset hxList
  simpa [prefixSet] using this

/-- The exact five-relation support-radius witness needs at least three prefix
chains.  This is the formal lower bound found by finite search. -/
theorem STRUCT_CHI3_prefix_cover_not_at_most_two :
    ¬ PrefixCoverDimensionAtMost (selectedRadius chi3F) 0 2 := by
  intro hDim
  rcases hDim with ⟨menu, hMenuCard, hCover⟩
  rcases hCover.2.2 2 (by norm_num) with ⟨r2, hr2, hopt2⟩
  rcases hCover.2.2 3 (by norm_num) with ⟨r3, hr3, hopt3⟩
  rcases hCover.2.2 4 (by norm_num) with ⟨r4, hr4, hopt4⟩
  have hp2 := chi3_unique_optimal_two _ hopt2
  have hp3 := chi3_unique_optimal_three _ hopt3
  have hp4 := chi3_unique_optimal_four _ hopt4
  have h23 : r2 ≠ r3 := by
    intro hEq
    subst r3
    have hsub := prefixSet_mono r2 (show 2 ≤ 3 by omega)
    rw [hp2, hp3] at hsub
    have hnot : ¬(({0, 2} : Finset (Fin 5)) ⊆ {0, 1, 4}) := by decide
    exact hnot hsub
  have h24 : r2 ≠ r4 := by
    intro hEq
    subst r4
    have hsub := prefixSet_mono r2 (show 2 ≤ 4 by omega)
    rw [hp2, hp4] at hsub
    have hnot : ¬(({0, 2} : Finset (Fin 5)) ⊆ {1, 2, 3, 4}) := by decide
    exact hnot hsub
  have h34 : r3 ≠ r4 := by
    intro hEq
    subst r4
    have hsub := prefixSet_mono r3 (show 3 ≤ 4 by omega)
    rw [hp3, hp4] at hsub
    have hnot : ¬(({0, 1, 4} : Finset (Fin 5)) ⊆ {1, 2, 3, 4}) := by decide
    exact hnot hsub
  have hthree : ({r2, r3, r4} : Finset (List (Fin 5))).card = 3 := by
    simp [h23, h24, h34]
  have hsubset : ({r2, r3, r4} : Finset (List (Fin 5))) ⊆ menu := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact hr2
    · exact hr3
    · exact hr4
  have hcardLower := Finset.card_le_card hsubset
  rw [hthree] at hcardLower
  omega


/- The finite arithmetic and the combinatorial three-chain contradiction are
   both discharged above; no search assumption remains in the headline. -/

end CIGAMF.P13.StructuralPrefixCoverChi3ProofAttempt
