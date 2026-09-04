import Mathlib
import «LeanStructuralOrdinaryChainCharacterizationV1»
import «LeanStructuralPrefixCoverChi3WitnessV1»

/-!
# Exact actual-support witness with prefix-cover dimension at least four

This integer-valued CIG support instance uses six relations and five support
states.  Exact finite evaluation proves four pairwise-incomparable unique
budget optima, hence no menu of three rankings covers every budget.
-/

namespace CIGAMF.P13.StructuralActualChi4Witness

open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.StructuralGeometryWitnesses
open CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralPrefixCoverChi3Witness

def chi4F : Fin 6 → Fin 5 → ℝ :=
  ![
    ![3, 4, 4, 1, -1],
    ![-2, 5, 1, -1, 1],
    ![-4, 2, -2, 4, -5],
    ![5, -4, 4, -4, -5],
    ![4, 0, -4, -5, 0],
    ![-2, -2, 2, -3, -4]
  ]

@[simp] private theorem fin6_compl_01 :
    ({0, 1} : Finset (Fin 6))ᶜ = {2, 3, 4, 5} := by decide

@[simp] private theorem fin6_compl_02 :
    ({0, 2} : Finset (Fin 6))ᶜ = {1, 3, 4, 5} := by decide

@[simp] private theorem fin6_compl_03 :
    ({0, 3} : Finset (Fin 6))ᶜ = {1, 2, 4, 5} := by decide

@[simp] private theorem fin6_compl_04 :
    ({0, 4} : Finset (Fin 6))ᶜ = {1, 2, 3, 5} := by decide

@[simp] private theorem fin6_compl_05 :
    ({0, 5} : Finset (Fin 6))ᶜ = {1, 2, 3, 4} := by decide

@[simp] private theorem fin6_compl_12 :
    ({1, 2} : Finset (Fin 6))ᶜ = {0, 3, 4, 5} := by decide

@[simp] private theorem fin6_compl_13 :
    ({1, 3} : Finset (Fin 6))ᶜ = {0, 2, 4, 5} := by decide

@[simp] private theorem fin6_compl_14 :
    ({1, 4} : Finset (Fin 6))ᶜ = {0, 2, 3, 5} := by decide

@[simp] private theorem fin6_compl_15 :
    ({1, 5} : Finset (Fin 6))ᶜ = {0, 2, 3, 4} := by decide

@[simp] private theorem fin6_compl_23 :
    ({2, 3} : Finset (Fin 6))ᶜ = {0, 1, 4, 5} := by decide

@[simp] private theorem fin6_compl_24 :
    ({2, 4} : Finset (Fin 6))ᶜ = {0, 1, 3, 5} := by decide

@[simp] private theorem fin6_compl_25 :
    ({2, 5} : Finset (Fin 6))ᶜ = {0, 1, 3, 4} := by decide

@[simp] private theorem fin6_compl_34 :
    ({3, 4} : Finset (Fin 6))ᶜ = {0, 1, 2, 5} := by decide

@[simp] private theorem fin6_compl_35 :
    ({3, 5} : Finset (Fin 6))ᶜ = {0, 1, 2, 4} := by decide

@[simp] private theorem fin6_compl_45 :
    ({4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2, 3} := by decide

@[simp] private theorem fin6_compl_012 :
    ({0, 1, 2} : Finset (Fin 6))ᶜ = {3, 4, 5} := by decide

@[simp] private theorem fin6_compl_013 :
    ({0, 1, 3} : Finset (Fin 6))ᶜ = {2, 4, 5} := by decide

@[simp] private theorem fin6_compl_014 :
    ({0, 1, 4} : Finset (Fin 6))ᶜ = {2, 3, 5} := by decide

@[simp] private theorem fin6_compl_015 :
    ({0, 1, 5} : Finset (Fin 6))ᶜ = {2, 3, 4} := by decide

@[simp] private theorem fin6_compl_023 :
    ({0, 2, 3} : Finset (Fin 6))ᶜ = {1, 4, 5} := by decide

@[simp] private theorem fin6_compl_024 :
    ({0, 2, 4} : Finset (Fin 6))ᶜ = {1, 3, 5} := by decide

@[simp] private theorem fin6_compl_025 :
    ({0, 2, 5} : Finset (Fin 6))ᶜ = {1, 3, 4} := by decide

@[simp] private theorem fin6_compl_034 :
    ({0, 3, 4} : Finset (Fin 6))ᶜ = {1, 2, 5} := by decide

@[simp] private theorem fin6_compl_035 :
    ({0, 3, 5} : Finset (Fin 6))ᶜ = {1, 2, 4} := by decide

@[simp] private theorem fin6_compl_045 :
    ({0, 4, 5} : Finset (Fin 6))ᶜ = {1, 2, 3} := by decide

@[simp] private theorem fin6_compl_123 :
    ({1, 2, 3} : Finset (Fin 6))ᶜ = {0, 4, 5} := by decide

@[simp] private theorem fin6_compl_124 :
    ({1, 2, 4} : Finset (Fin 6))ᶜ = {0, 3, 5} := by decide

@[simp] private theorem fin6_compl_125 :
    ({1, 2, 5} : Finset (Fin 6))ᶜ = {0, 3, 4} := by decide

@[simp] private theorem fin6_compl_134 :
    ({1, 3, 4} : Finset (Fin 6))ᶜ = {0, 2, 5} := by decide

@[simp] private theorem fin6_compl_135 :
    ({1, 3, 5} : Finset (Fin 6))ᶜ = {0, 2, 4} := by decide

@[simp] private theorem fin6_compl_145 :
    ({1, 4, 5} : Finset (Fin 6))ᶜ = {0, 2, 3} := by decide

@[simp] private theorem fin6_compl_234 :
    ({2, 3, 4} : Finset (Fin 6))ᶜ = {0, 1, 5} := by decide

@[simp] private theorem fin6_compl_235 :
    ({2, 3, 5} : Finset (Fin 6))ᶜ = {0, 1, 4} := by decide

@[simp] private theorem fin6_compl_245 :
    ({2, 4, 5} : Finset (Fin 6))ᶜ = {0, 1, 3} := by decide

@[simp] private theorem fin6_compl_345 :
    ({3, 4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2} := by decide

@[simp] private theorem radius_01 :
    selectedRadius chi4F ({0, 1} : Finset (Fin 6)) =
      (3 - (-14 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 1} 3 (-14)
    (by intro a; rw [fin6_compl_01]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_01]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    0 4
    (by rw [fin6_compl_01]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_01]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_02 :
    selectedRadius chi4F ({0, 2} : Finset (Fin 6)) =
      (5 - (-13 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 2} 5 (-13)
    (by intro a; rw [fin6_compl_02]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_02]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    0 3
    (by rw [fin6_compl_02]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_02]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_03 :
    selectedRadius chi4F ({0, 3} : Finset (Fin 6)) =
      (5 - (-8 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 3} 5 (-8)
    (by intro a; rw [fin6_compl_03]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_03]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 4
    (by rw [fin6_compl_03]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_03]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_04 :
    selectedRadius chi4F ({0, 4} : Finset (Fin 6)) =
      (5 - (-13 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 4} 5 (-13)
    (by intro a; rw [fin6_compl_04]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_04]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    2 4
    (by rw [fin6_compl_04]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_04]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_05 :
    selectedRadius chi4F ({0, 5} : Finset (Fin 6)) =
      (3 - (-9 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 5} 3 (-9)
    (by intro a; rw [fin6_compl_05]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_05]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    0 4
    (by rw [fin6_compl_05]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_05]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_12 :
    selectedRadius chi4F ({1, 2} : Finset (Fin 6)) =
      (10 - (-11 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {1, 2} 10 (-11)
    (by intro a; rw [fin6_compl_12]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_12]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    0 3
    (by rw [fin6_compl_12]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_12]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_13 :
    selectedRadius chi4F ({1, 3} : Finset (Fin 6)) =
      (4 - (-10 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {1, 3} 4 (-10)
    (by intro a; rw [fin6_compl_13]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_13]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 4
    (by rw [fin6_compl_13]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_13]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_14 :
    selectedRadius chi4F ({1, 4} : Finset (Fin 6)) =
      (8 - (-15 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {1, 4} 8 (-15)
    (by intro a; rw [fin6_compl_14]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_14]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    2 4
    (by rw [fin6_compl_14]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_14]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_15 :
    selectedRadius chi4F ({1, 5} : Finset (Fin 6)) =
      (8 - (-11 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {1, 5} 8 (-11)
    (by intro a; rw [fin6_compl_15]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_15]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    0 4
    (by rw [fin6_compl_15]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_15]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_23 :
    selectedRadius chi4F ({2, 3} : Finset (Fin 6)) =
      (7 - (-8 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {2, 3} 7 (-8)
    (by intro a; rw [fin6_compl_23]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_23]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 3
    (by rw [fin6_compl_23]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_23]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_24 :
    selectedRadius chi4F ({2, 4} : Finset (Fin 6)) =
      (11 - (-9 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {2, 4} 11 (-9)
    (by intro a; rw [fin6_compl_24]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_24]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    2 4
    (by rw [fin6_compl_24]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_24]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_25 :
    selectedRadius chi4F ({2, 5} : Finset (Fin 6)) =
      (10 - (-9 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {2, 5} 10 (-9)
    (by intro a; rw [fin6_compl_25]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_25]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    0 3
    (by rw [fin6_compl_25]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_25]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_34 :
    selectedRadius chi4F ({3, 4} : Finset (Fin 6)) =
      (9 - (-9 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {3, 4} 9 (-9)
    (by intro a; rw [fin6_compl_34]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_34]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 4
    (by rw [fin6_compl_34]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_34]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_35 :
    selectedRadius chi4F ({3, 5} : Finset (Fin 6)) =
      (11 - (-5 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {3, 5} 11 (-5)
    (by intro a; rw [fin6_compl_35]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_35]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 4
    (by rw [fin6_compl_35]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_35]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_45 :
    selectedRadius chi4F ({4, 5} : Finset (Fin 6)) =
      (7 - (-10 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {4, 5} 7 (-10)
    (by intro a; rw [fin6_compl_45]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_45]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 4
    (by rw [fin6_compl_45]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_45]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_012 :
    selectedRadius chi4F ({0, 1, 2} : Finset (Fin 6)) =
      (7 - (-12 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 1, 2} 7 (-12)
    (by intro a; rw [fin6_compl_012]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_012]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    0 3
    (by rw [fin6_compl_012]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_012]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_013 :
    selectedRadius chi4F ({0, 1, 3} : Finset (Fin 6)) =
      (0 - (-9 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 1, 3} 0 (-9)
    (by intro a; rw [fin6_compl_013]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_013]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 4
    (by rw [fin6_compl_013]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_013]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_014 :
    selectedRadius chi4F ({0, 1, 4} : Finset (Fin 6)) =
      (4 - (-14 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 1, 4} 4 (-14)
    (by intro a; rw [fin6_compl_014]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_014]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    2 4
    (by rw [fin6_compl_014]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_014]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_015 :
    selectedRadius chi4F ({0, 1, 5} : Finset (Fin 6)) =
      (5 - (-10 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 1, 5} 5 (-10)
    (by intro a; rw [fin6_compl_015]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_015]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    0 4
    (by rw [fin6_compl_015]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_015]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_023 :
    selectedRadius chi4F ({0, 2, 3} : Finset (Fin 6)) =
      (3 - (-9 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 2, 3} 3 (-9)
    (by intro a; rw [fin6_compl_023]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_023]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 3
    (by rw [fin6_compl_023]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_023]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_024 :
    selectedRadius chi4F ({0, 2, 4} : Finset (Fin 6)) =
      (7 - (-8 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 2, 4} 7 (-8)
    (by intro a; rw [fin6_compl_024]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_024]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    2 3
    (by rw [fin6_compl_024]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_024]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_025 :
    selectedRadius chi4F ({0, 2, 5} : Finset (Fin 6)) =
      (7 - (-10 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 2, 5} 7 (-10)
    (by intro a; rw [fin6_compl_025]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_025]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    0 3
    (by rw [fin6_compl_025]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_025]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_034 :
    selectedRadius chi4F ({0, 3, 4} : Finset (Fin 6)) =
      (5 - (-8 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 3, 4} 5 (-8)
    (by intro a; rw [fin6_compl_034]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_034]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 0
    (by rw [fin6_compl_034]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_034]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_035 :
    selectedRadius chi4F ({0, 3, 5} : Finset (Fin 6)) =
      (7 - (-5 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 3, 5} 7 (-5)
    (by intro a; rw [fin6_compl_035]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_035]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 2
    (by rw [fin6_compl_035]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_035]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_045 :
    selectedRadius chi4F ({0, 4, 5} : Finset (Fin 6)) =
      (3 - (-9 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {0, 4, 5} 3 (-9)
    (by intro a; rw [fin6_compl_045]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_045]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 4
    (by rw [fin6_compl_045]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_045]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_123 :
    selectedRadius chi4F ({1, 2, 3} : Finset (Fin 6)) =
      (5 - (-7 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {1, 2, 3} 5 (-7)
    (by intro a; rw [fin6_compl_123]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_123]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    0 3
    (by rw [fin6_compl_123]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_123]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_124 :
    selectedRadius chi4F ({1, 2, 4} : Finset (Fin 6)) =
      (10 - (-10 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {1, 2, 4} 10 (-10)
    (by intro a; rw [fin6_compl_124]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_124]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    2 4
    (by rw [fin6_compl_124]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_124]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_125 :
    selectedRadius chi4F ({1, 2, 5} : Finset (Fin 6)) =
      (12 - (-8 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {1, 2, 5} 12 (-8)
    (by intro a; rw [fin6_compl_125]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_125]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    0 3
    (by rw [fin6_compl_125]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_125]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_134 :
    selectedRadius chi4F ({1, 3, 4} : Finset (Fin 6)) =
      (4 - (-10 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {1, 3, 4} 4 (-10)
    (by intro a; rw [fin6_compl_134]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_134]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 4
    (by rw [fin6_compl_134]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_134]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_135 :
    selectedRadius chi4F ({1, 3, 5} : Finset (Fin 6)) =
      (6 - (-6 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {1, 3, 5} 6 (-6)
    (by intro a; rw [fin6_compl_135]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_135]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 4
    (by rw [fin6_compl_135]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_135]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_145 :
    selectedRadius chi4F ({1, 4, 5} : Finset (Fin 6)) =
      (6 - (-11 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {1, 4, 5} 6 (-11)
    (by intro a; rw [fin6_compl_145]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_145]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    2 4
    (by rw [fin6_compl_145]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_145]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_234 :
    selectedRadius chi4F ({2, 3, 4} : Finset (Fin 6)) =
      (7 - (-4 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {2, 3, 4} 7 (-4)
    (by intro a; rw [fin6_compl_234]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_234]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 4
    (by rw [fin6_compl_234]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_234]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_235 :
    selectedRadius chi4F ({2, 3, 5} : Finset (Fin 6)) =
      (9 - (-5 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {2, 3, 5} 9 (-5)
    (by intro a; rw [fin6_compl_235]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_235]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 3
    (by rw [fin6_compl_235]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_235]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_245 :
    selectedRadius chi4F ({2, 4, 5} : Finset (Fin 6)) =
      (9 - (-5 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {2, 4, 5} 9 (-5)
    (by intro a; rw [fin6_compl_245]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_245]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    2 4
    (by rw [fin6_compl_245]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_245]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_345 :
    selectedRadius chi4F ({3, 4, 5} : Finset (Fin 6)) =
      (11 - (-5 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F {3, 4, 5} 11 (-5)
    (by intro a; rw [fin6_compl_345]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; rw [fin6_compl_345]; fin_cases a <;>
      simp [sumComponent, chi4F] <;> norm_num)
    1 4
    (by rw [fin6_compl_345]; simp [sumComponent, chi4F] <;> norm_num)
    (by rw [fin6_compl_345]; simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_01 :
    selectedRadius chi4F (({0, 1} : Finset (Fin 6))ᶜ) =
      (9 - (0 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({0, 1}ᶜ) 9 0
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    1 3
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_02 :
    selectedRadius chi4F (({0, 2} : Finset (Fin 6))ᶜ) =
      (6 - (-6 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({0, 2}ᶜ) 6 (-6)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    1 4
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_03 :
    selectedRadius chi4F (({0, 3} : Finset (Fin 6))ᶜ) =
      (8 - (-6 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({0, 3}ᶜ) 8 (-6)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    0 4
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_04 :
    selectedRadius chi4F (({0, 4} : Finset (Fin 6))ᶜ) =
      (7 - (-4 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({0, 4}ᶜ) 7 (-4)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    0 3
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_05 :
    selectedRadius chi4F (({0, 5} : Finset (Fin 6))ᶜ) =
      (6 - (-5 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({0, 5}ᶜ) 6 (-5)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    2 4
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_12 :
    selectedRadius chi4F (({1, 2} : Finset (Fin 6))ᶜ) =
      (7 - (-6 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({1, 2}ᶜ) 7 (-6)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    1 0
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_13 :
    selectedRadius chi4F (({1, 3} : Finset (Fin 6))ᶜ) =
      (5 - (-5 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({1, 3}ᶜ) 5 (-5)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    2 3
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_14 :
    selectedRadius chi4F (({1, 4} : Finset (Fin 6))ᶜ) =
      (5 - (-6 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({1, 4}ᶜ) 5 (-6)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    1 3
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_15 :
    selectedRadius chi4F (({1, 5} : Finset (Fin 6))ᶜ) =
      (3 - (-4 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({1, 5}ᶜ) 3 (-4)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    1 0
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_23 :
    selectedRadius chi4F (({2, 3} : Finset (Fin 6))ᶜ) =
      (2 - (-10 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({2, 3}ᶜ) 2 (-10)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    2 4
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_24 :
    selectedRadius chi4F (({2, 4} : Finset (Fin 6))ᶜ) =
      (2 - (-6 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({2, 4}ᶜ) 2 (-6)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    1 2
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_25 :
    selectedRadius chi4F (({2, 5} : Finset (Fin 6))ᶜ) =
      (1 - (-9 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({2, 5}ᶜ) 1 (-9)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    3 4
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_34 :
    selectedRadius chi4F (({3, 4} : Finset (Fin 6))ᶜ) =
      (9 - (-9 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({3, 4}ᶜ) 9 (-9)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    0 3
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_35 :
    selectedRadius chi4F (({3, 5} : Finset (Fin 6))ᶜ) =
      (6 - (-9 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({3, 5}ᶜ) 6 (-9)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    2 4
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_45 :
    selectedRadius chi4F (({4, 5} : Finset (Fin 6))ᶜ) =
      (2 - (-8 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({4, 5}ᶜ) 2 (-8)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    0 3
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_0 :
    selectedRadius chi4F (({0} : Finset (Fin 6))ᶜ) =
      (4 - (-1 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({0}ᶜ) 4 (-1)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    1 4
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_1 :
    selectedRadius chi4F (({1} : Finset (Fin 6))ᶜ) =
      (5 - (-2 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({1}ᶜ) 5 (-2)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    1 0
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_2 :
    selectedRadius chi4F (({2} : Finset (Fin 6))ᶜ) =
      (4 - (-5 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({2}ᶜ) 4 (-5)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    3 4
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_3 :
    selectedRadius chi4F (({3} : Finset (Fin 6))ᶜ) =
      (5 - (-5 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({3}ᶜ) 5 (-5)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    0 4
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_4 :
    selectedRadius chi4F (({4} : Finset (Fin 6))ᶜ) =
      (4 - (-5 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({4}ᶜ) 4 (-5)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    0 3
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

@[simp] private theorem radius_compl_5 :
    selectedRadius chi4F (({5} : Finset (Fin 6))ᶜ) =
      (2 - (-4 : ℝ)) / 2 := by
  exact selectedRadius_from_extrema chi4F ({5}ᶜ) 2 (-4)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    (by intro a; fin_cases a <;> simp [sumComponent, chi4F] <;> norm_num)
    2 4
    (by simp [sumComponent, chi4F] <;> norm_num)
    (by simp [sumComponent, chi4F] <;> norm_num)

/- Legacy element-by-element cardinal decompositions are retained as proof
design history.  The compiled proof below uses closed finite cardinal-case
theorems, avoiding irrelevant ordering artifacts of finset literals.

private theorem chi4_unique_optimal_two
    (S : Finset (Fin 6))
    (hS : EpsilonOptimalAt (selectedRadius chi4F) 0 2 S) :
    S = ({0, 5} : Finset (Fin 6)) := by
  have hle := hS.2 ({0, 5} : Finset (Fin 6)) (by decide)
  rcases Finset.card_eq_two.mp hS.1 with ⟨a, b, hab, rfl⟩
  fin_cases a <;> fin_cases b <;>
    simp_all [Finset.insert_comm,
      radius_01,
      radius_02,
      radius_03,
      radius_04,
      radius_05,
      radius_12,
      radius_13,
      radius_14,
      radius_15,
      radius_23,
      radius_24,
      radius_25,
      radius_34,
      radius_35,
      radius_45] <;> norm_num at hle

private theorem chi4_unique_optimal_three
    (S : Finset (Fin 6))
    (hS : EpsilonOptimalAt (selectedRadius chi4F) 0 3 S) :
    S = ({0, 1, 3} : Finset (Fin 6)) := by
  have hle := hS.2 ({0, 1, 3} : Finset (Fin 6)) (by decide)
  rcases Finset.card_eq_three.mp hS.1 with ⟨a, b, c, hab, hac, hbc, rfl⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp_all [Finset.insert_comm,
      radius_012,
      radius_013,
      radius_014,
      radius_015,
      radius_023,
      radius_024,
      radius_025,
      radius_034,
      radius_035,
      radius_045,
      radius_123,
      radius_124,
      radius_125,
      radius_134,
      radius_135,
      radius_145,
      radius_234,
      radius_235,
      radius_245,
      radius_345] <;> norm_num at hle

private theorem chi4_unique_optimal_four
    (S : Finset (Fin 6))
    (hS : EpsilonOptimalAt (selectedRadius chi4F) 0 4 S) :
    S = ({0, 2, 3, 4} : Finset (Fin 6)) := by
  have hle := hS.2 ({0, 2, 3, 4} : Finset (Fin 6)) (by decide)
  have hcompCard : Sᶜ.card = 2 := by
    simp [Finset.card_compl, hS.1]
  rcases Finset.card_eq_two.mp hcompCard with ⟨a, b, hab, hcomp⟩
  have hrepr : S = ({a, b} : Finset (Fin 6))ᶜ := by
    rw [← hcomp, compl_compl]
  rw [hrepr] at hle ⊢
  fin_cases a <;> fin_cases b <;>
    simp_all [Finset.insert_comm,
      radius_compl_01,
      radius_compl_02,
      radius_compl_03,
      radius_compl_04,
      radius_compl_05,
      radius_compl_12,
      radius_compl_13,
      radius_compl_14,
      radius_compl_15,
      radius_compl_23,
      radius_compl_24,
      radius_compl_25,
      radius_compl_34,
      radius_compl_35,
      radius_compl_45] <;> norm_num at hle

private theorem chi4_unique_optimal_five
    (S : Finset (Fin 6))
    (hS : EpsilonOptimalAt (selectedRadius chi4F) 0 5 S) :
    S = ({1, 2, 3, 4, 5} : Finset (Fin 6)) := by
  have hle := hS.2 ({1, 2, 3, 4, 5} : Finset (Fin 6)) (by decide)
  have hcompCard : Sᶜ.card = 1 := by
    simp [Finset.card_compl, hS.1]
  rcases Finset.card_eq_one.mp hcompCard with ⟨a, hcomp⟩
  have hrepr : S = ({a} : Finset (Fin 6))ᶜ := by
    rw [← hcomp, compl_compl]
  rw [hrepr] at hle ⊢
  fin_cases a <;> simp_all [radius_compl_0,
      radius_compl_1,
      radius_compl_2,
      radius_compl_3,
      radius_compl_4,
      radius_compl_5] <;> norm_num at hle

-/

@[simp] private theorem radius_0123 :
    selectedRadius chi4F ({0, 1, 2, 3} : Finset (Fin 6)) =
      (2 - (-8 : ℝ)) / 2 := by
  rw [show ({0, 1, 2, 3} : Finset (Fin 6)) =
    ({4, 5} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_45

@[simp] private theorem radius_0124 :
    selectedRadius chi4F ({0, 1, 2, 4} : Finset (Fin 6)) =
      (6 - (-9 : ℝ)) / 2 := by
  rw [show ({0, 1, 2, 4} : Finset (Fin 6)) =
    ({3, 5} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_35

@[simp] private theorem radius_0125 :
    selectedRadius chi4F ({0, 1, 2, 5} : Finset (Fin 6)) =
      (9 - (-9 : ℝ)) / 2 := by
  rw [show ({0, 1, 2, 5} : Finset (Fin 6)) =
    ({3, 4} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_34

@[simp] private theorem radius_0134 :
    selectedRadius chi4F ({0, 1, 3, 4} : Finset (Fin 6)) =
      (1 - (-9 : ℝ)) / 2 := by
  rw [show ({0, 1, 3, 4} : Finset (Fin 6)) =
    ({2, 5} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_25

@[simp] private theorem radius_0135 :
    selectedRadius chi4F ({0, 1, 3, 5} : Finset (Fin 6)) =
      (2 - (-6 : ℝ)) / 2 := by
  rw [show ({0, 1, 3, 5} : Finset (Fin 6)) =
    ({2, 4} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_24

@[simp] private theorem radius_0145 :
    selectedRadius chi4F ({0, 1, 4, 5} : Finset (Fin 6)) =
      (2 - (-10 : ℝ)) / 2 := by
  rw [show ({0, 1, 4, 5} : Finset (Fin 6)) =
    ({2, 3} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_23

@[simp] private theorem radius_0234 :
    selectedRadius chi4F ({0, 2, 3, 4} : Finset (Fin 6)) =
      (3 - (-4 : ℝ)) / 2 := by
  rw [show ({0, 2, 3, 4} : Finset (Fin 6)) =
    ({1, 5} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_15

@[simp] private theorem radius_0235 :
    selectedRadius chi4F ({0, 2, 3, 5} : Finset (Fin 6)) =
      (5 - (-6 : ℝ)) / 2 := by
  rw [show ({0, 2, 3, 5} : Finset (Fin 6)) =
    ({1, 4} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_14

@[simp] private theorem radius_0245 :
    selectedRadius chi4F ({0, 2, 4, 5} : Finset (Fin 6)) =
      (5 - (-5 : ℝ)) / 2 := by
  rw [show ({0, 2, 4, 5} : Finset (Fin 6)) =
    ({1, 3} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_13

@[simp] private theorem radius_0345 :
    selectedRadius chi4F ({0, 3, 4, 5} : Finset (Fin 6)) =
      (7 - (-6 : ℝ)) / 2 := by
  rw [show ({0, 3, 4, 5} : Finset (Fin 6)) =
    ({1, 2} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_12

@[simp] private theorem radius_1234 :
    selectedRadius chi4F ({1, 2, 3, 4} : Finset (Fin 6)) =
      (6 - (-5 : ℝ)) / 2 := by
  rw [show ({1, 2, 3, 4} : Finset (Fin 6)) =
    ({0, 5} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_05

@[simp] private theorem radius_1235 :
    selectedRadius chi4F ({1, 2, 3, 5} : Finset (Fin 6)) =
      (7 - (-4 : ℝ)) / 2 := by
  rw [show ({1, 2, 3, 5} : Finset (Fin 6)) =
    ({0, 4} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_04

@[simp] private theorem radius_1245 :
    selectedRadius chi4F ({1, 2, 4, 5} : Finset (Fin 6)) =
      (8 - (-6 : ℝ)) / 2 := by
  rw [show ({1, 2, 4, 5} : Finset (Fin 6)) =
    ({0, 3} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_03

@[simp] private theorem radius_1345 :
    selectedRadius chi4F ({1, 3, 4, 5} : Finset (Fin 6)) =
      (6 - (-6 : ℝ)) / 2 := by
  rw [show ({1, 3, 4, 5} : Finset (Fin 6)) =
    ({0, 2} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_02

@[simp] private theorem radius_2345 :
    selectedRadius chi4F ({2, 3, 4, 5} : Finset (Fin 6)) =
      (9 - (0 : ℝ)) / 2 := by
  rw [show ({2, 3, 4, 5} : Finset (Fin 6)) =
    ({0, 1} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_01

@[simp] private theorem radius_01234 :
    selectedRadius chi4F ({0, 1, 2, 3, 4} : Finset (Fin 6)) =
      (2 - (-4 : ℝ)) / 2 := by
  rw [show ({0, 1, 2, 3, 4} : Finset (Fin 6)) =
    ({5} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_5

@[simp] private theorem radius_01235 :
    selectedRadius chi4F ({0, 1, 2, 3, 5} : Finset (Fin 6)) =
      (4 - (-5 : ℝ)) / 2 := by
  rw [show ({0, 1, 2, 3, 5} : Finset (Fin 6)) =
    ({4} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_4

@[simp] private theorem radius_01245 :
    selectedRadius chi4F ({0, 1, 2, 4, 5} : Finset (Fin 6)) =
      (5 - (-5 : ℝ)) / 2 := by
  rw [show ({0, 1, 2, 4, 5} : Finset (Fin 6)) =
    ({3} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_3

@[simp] private theorem radius_01345 :
    selectedRadius chi4F ({0, 1, 3, 4, 5} : Finset (Fin 6)) =
      (4 - (-5 : ℝ)) / 2 := by
  rw [show ({0, 1, 3, 4, 5} : Finset (Fin 6)) =
    ({2} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_2

@[simp] private theorem radius_02345 :
    selectedRadius chi4F ({0, 2, 3, 4, 5} : Finset (Fin 6)) =
      (5 - (-2 : ℝ)) / 2 := by
  rw [show ({0, 2, 3, 4, 5} : Finset (Fin 6)) =
    ({1} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_1

@[simp] private theorem radius_12345 :
    selectedRadius chi4F ({1, 2, 3, 4, 5} : Finset (Fin 6)) =
      (4 - (-1 : ℝ)) / 2 := by
  rw [show ({1, 2, 3, 4, 5} : Finset (Fin 6)) =
    ({0} : Finset (Fin 6))ᶜ by decide]
  exact radius_compl_0

private theorem fin6_card2_cases :
    ∀ S : Finset (Fin 6), S.card = 2 →
      S = ({0, 1} : Finset (Fin 6)) ∨
      S = ({0, 2} : Finset (Fin 6)) ∨
      S = ({0, 3} : Finset (Fin 6)) ∨
      S = ({0, 4} : Finset (Fin 6)) ∨
      S = ({0, 5} : Finset (Fin 6)) ∨
      S = ({1, 2} : Finset (Fin 6)) ∨
      S = ({1, 3} : Finset (Fin 6)) ∨
      S = ({1, 4} : Finset (Fin 6)) ∨
      S = ({1, 5} : Finset (Fin 6)) ∨
      S = ({2, 3} : Finset (Fin 6)) ∨
      S = ({2, 4} : Finset (Fin 6)) ∨
      S = ({2, 5} : Finset (Fin 6)) ∨
      S = ({3, 4} : Finset (Fin 6)) ∨
      S = ({3, 5} : Finset (Fin 6)) ∨
      S = ({4, 5} : Finset (Fin 6)) := by
  native_decide

private theorem fin6_card3_cases :
    ∀ S : Finset (Fin 6), S.card = 3 →
      S = ({0, 1, 2} : Finset (Fin 6)) ∨
      S = ({0, 1, 3} : Finset (Fin 6)) ∨
      S = ({0, 1, 4} : Finset (Fin 6)) ∨
      S = ({0, 1, 5} : Finset (Fin 6)) ∨
      S = ({0, 2, 3} : Finset (Fin 6)) ∨
      S = ({0, 2, 4} : Finset (Fin 6)) ∨
      S = ({0, 2, 5} : Finset (Fin 6)) ∨
      S = ({0, 3, 4} : Finset (Fin 6)) ∨
      S = ({0, 3, 5} : Finset (Fin 6)) ∨
      S = ({0, 4, 5} : Finset (Fin 6)) ∨
      S = ({1, 2, 3} : Finset (Fin 6)) ∨
      S = ({1, 2, 4} : Finset (Fin 6)) ∨
      S = ({1, 2, 5} : Finset (Fin 6)) ∨
      S = ({1, 3, 4} : Finset (Fin 6)) ∨
      S = ({1, 3, 5} : Finset (Fin 6)) ∨
      S = ({1, 4, 5} : Finset (Fin 6)) ∨
      S = ({2, 3, 4} : Finset (Fin 6)) ∨
      S = ({2, 3, 5} : Finset (Fin 6)) ∨
      S = ({2, 4, 5} : Finset (Fin 6)) ∨
      S = ({3, 4, 5} : Finset (Fin 6)) := by
  native_decide

private theorem fin6_card4_cases :
    ∀ S : Finset (Fin 6), S.card = 4 →
      S = ({0, 1, 2, 3} : Finset (Fin 6)) ∨
      S = ({0, 1, 2, 4} : Finset (Fin 6)) ∨
      S = ({0, 1, 2, 5} : Finset (Fin 6)) ∨
      S = ({0, 1, 3, 4} : Finset (Fin 6)) ∨
      S = ({0, 1, 3, 5} : Finset (Fin 6)) ∨
      S = ({0, 1, 4, 5} : Finset (Fin 6)) ∨
      S = ({0, 2, 3, 4} : Finset (Fin 6)) ∨
      S = ({0, 2, 3, 5} : Finset (Fin 6)) ∨
      S = ({0, 2, 4, 5} : Finset (Fin 6)) ∨
      S = ({0, 3, 4, 5} : Finset (Fin 6)) ∨
      S = ({1, 2, 3, 4} : Finset (Fin 6)) ∨
      S = ({1, 2, 3, 5} : Finset (Fin 6)) ∨
      S = ({1, 2, 4, 5} : Finset (Fin 6)) ∨
      S = ({1, 3, 4, 5} : Finset (Fin 6)) ∨
      S = ({2, 3, 4, 5} : Finset (Fin 6)) := by
  native_decide

private theorem fin6_card5_cases :
    ∀ S : Finset (Fin 6), S.card = 5 →
      S = ({0, 1, 2, 3, 4} : Finset (Fin 6)) ∨
      S = ({0, 1, 2, 3, 5} : Finset (Fin 6)) ∨
      S = ({0, 1, 2, 4, 5} : Finset (Fin 6)) ∨
      S = ({0, 1, 3, 4, 5} : Finset (Fin 6)) ∨
      S = ({0, 2, 3, 4, 5} : Finset (Fin 6)) ∨
      S = ({1, 2, 3, 4, 5} : Finset (Fin 6)) := by
  native_decide

private theorem chi4_unique_optimal_two
    (S : Finset (Fin 6))
    (hS : EpsilonOptimalAt (selectedRadius chi4F) 0 2 S) :
    S = ({0, 5} : Finset (Fin 6)) := by
  have hle := hS.2 ({0, 5} : Finset (Fin 6)) (by decide)
  rcases fin6_card2_cases S hS.1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst S
  all_goals first | exact rfl | norm_num at hle

private theorem chi4_unique_optimal_three
    (S : Finset (Fin 6))
    (hS : EpsilonOptimalAt (selectedRadius chi4F) 0 3 S) :
    S = ({0, 1, 3} : Finset (Fin 6)) := by
  have hle := hS.2 ({0, 1, 3} : Finset (Fin 6)) (by decide)
  rcases fin6_card3_cases S hS.1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst S
  all_goals first | exact rfl | norm_num at hle

private theorem chi4_unique_optimal_four
    (S : Finset (Fin 6))
    (hS : EpsilonOptimalAt (selectedRadius chi4F) 0 4 S) :
    S = ({0, 2, 3, 4} : Finset (Fin 6)) := by
  have hle := hS.2 ({0, 2, 3, 4} : Finset (Fin 6)) (by decide)
  rcases fin6_card4_cases S hS.1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst S
  all_goals first | exact rfl | norm_num at hle

private theorem chi4_unique_optimal_five
    (S : Finset (Fin 6))
    (hS : EpsilonOptimalAt (selectedRadius chi4F) 0 5 S) :
    S = ({1, 2, 3, 4, 5} : Finset (Fin 6)) := by
  have hle := hS.2 ({1, 2, 3, 4, 5} : Finset (Fin 6)) (by decide)
  rcases fin6_card5_cases S hS.1 with h | h | h | h | h | h <;>
    subst S
  all_goals first | exact rfl | norm_num at hle


private theorem prefixSet_mono
    (ranking : List (Fin 6)) {k l : ℕ} (hkl : k ≤ l) :
    prefixSet ranking k ⊆ prefixSet ranking l := by
  intro x hx
  have hp : ranking.take k <+: ranking.take l :=
    List.take_prefix_take_left hkl
  have hxList : x ∈ ranking.take k := by
    simpa [prefixSet] using hx
  have : x ∈ ranking.take l := hp.subset hxList
  simpa [prefixSet] using this

theorem STRUCT_ACTUAL_CHI4_prefix_cover_not_at_most_three :
    ¬ PrefixCoverDimensionAtMost (selectedRadius chi4F) 0 3 := by
  intro hDim
  rcases hDim with ⟨menu, hMenuCard, hCover⟩
  rcases hCover.2.2 2 (by norm_num) with ⟨r2, hr2, hopt2⟩
  rcases hCover.2.2 3 (by norm_num) with ⟨r3, hr3, hopt3⟩
  rcases hCover.2.2 4 (by norm_num) with ⟨r4, hr4, hopt4⟩
  rcases hCover.2.2 5 (by norm_num) with ⟨r5, hr5, hopt5⟩
  have hp2 := chi4_unique_optimal_two _ hopt2
  have hp3 := chi4_unique_optimal_three _ hopt3
  have hp4 := chi4_unique_optimal_four _ hopt4
  have hp5 := chi4_unique_optimal_five _ hopt5
  have h23 : r2 ≠ r3 := by
    intro h; subst r3
    have hsub := prefixSet_mono r2 (show 2 ≤ 3 by omega)
    rw [hp2, hp3] at hsub
    exact (by decide : ¬(({0, 5} : Finset (Fin 6)) ⊆ {0, 1, 3})) hsub
  have h24 : r2 ≠ r4 := by
    intro h; subst r4
    have hsub := prefixSet_mono r2 (show 2 ≤ 4 by omega)
    rw [hp2, hp4] at hsub
    exact (by decide : ¬(({0, 5} : Finset (Fin 6)) ⊆ {0, 2, 3, 4})) hsub
  have h25 : r2 ≠ r5 := by
    intro h; subst r5
    have hsub := prefixSet_mono r2 (show 2 ≤ 5 by omega)
    rw [hp2, hp5] at hsub
    exact (by decide : ¬(({0, 5} : Finset (Fin 6)) ⊆ {1, 2, 3, 4, 5})) hsub
  have h34 : r3 ≠ r4 := by
    intro h; subst r4
    have hsub := prefixSet_mono r3 (show 3 ≤ 4 by omega)
    rw [hp3, hp4] at hsub
    exact (by decide : ¬(({0, 1, 3} : Finset (Fin 6)) ⊆ {0, 2, 3, 4})) hsub
  have h35 : r3 ≠ r5 := by
    intro h; subst r5
    have hsub := prefixSet_mono r3 (show 3 ≤ 5 by omega)
    rw [hp3, hp5] at hsub
    exact (by decide : ¬(({0, 1, 3} : Finset (Fin 6)) ⊆ {1, 2, 3, 4, 5})) hsub
  have h45 : r4 ≠ r5 := by
    intro h; subst r5
    have hsub := prefixSet_mono r4 (show 4 ≤ 5 by omega)
    rw [hp4, hp5] at hsub
    exact (by decide : ¬(({0, 2, 3, 4} : Finset (Fin 6)) ⊆ {1, 2, 3, 4, 5})) hsub
  have hfour :
      ({r2, r3, r4, r5} : Finset (List (Fin 6))).card = 4 := by
    simp [h23, h24, h25, h34, h35, h45]
  have hsubset :
      ({r2, r3, r4, r5} : Finset (List (Fin 6))) ⊆ menu := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hr2
    · exact hr3
    · exact hr4
    · exact hr5
  have hcardLower := Finset.card_le_card hsubset
  rw [hfour] at hcardLower
  omega

end CIGAMF.P13.StructuralActualChi4Witness
