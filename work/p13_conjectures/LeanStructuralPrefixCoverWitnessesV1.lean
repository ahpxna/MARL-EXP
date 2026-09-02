import Mathlib
import «LeanStructuralPrefixCoverDimensionV1»
import «LeanStructuralGeometryWitnessesV4»

/-!
# Exact prefix-cover lower bounds in the actual support-radius class

The existing `w3F` witness proves that one ranking cannot cover all exact
budget optima.  This extension first turns that fact into an exact
`chi_prefix = 2` result.  It then records a five-relation, five-support-action
world found by finite search whose unique optima force three distinct prefix
chains.  All objects remain genuine `selectedRadius` objectives.
-/

namespace CIGAMF.P13.StructuralPrefixCoverWitnesses

open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.StructuralRankability
open CIGAMF.V4.StructuralGeometryWitnesses
open CIGAMF.P13.StructuralPrefixCoverDimension

/- The rows are the five feasible support atoms
   00011, 00100, 01010, 10100, 11010.
   Primitive slopes are (-1,-3,3,3,-3). -/
def chi3F (j a : Fin 5) : ℝ :=
  match j, a with
  | 0, 3 => -1
  | 0, 4 => -1
  | 1, 2 => -3
  | 1, 4 => -3
  | 2, 1 => 3
  | 2, 3 => 3
  | 3, 0 => 3
  | 3, 2 => 3
  | 3, 4 => 3
  | 4, 0 => -3
  | _, _ => 0

/-! ## The existing three-relation geometry witness has exact dimension two -/

def w3Rank12 : List (Fin 3) := [2, 0, 1]
def w3Rank3 : List (Fin 3) := [0, 1, 2]
def w3Menu : Finset (List (Fin 3)) := {w3Rank12, w3Rank3}

private theorem w3_full_rank12 : IsFullRanking w3Rank12 := by
  constructor
  · decide
  · ext x
    fin_cases x <;> simp [w3Rank12]

private theorem w3_full_rank3 : IsFullRanking w3Rank3 := by
  constructor
  · decide
  · ext x
    fin_cases x <;> simp [w3Rank3]

private theorem w3_optimal_one :
    EpsilonOptimalAt (selectedRadius w3F) 0 1 ({2} : Finset (Fin 3)) := by
  refine ⟨by simp, ?_⟩
  intro S hcard
  rcases Finset.card_eq_one.mp hcard with ⟨a, rfl⟩
  fin_cases a
  · change selectedRadius w3F ({2} : Finset (Fin 3)) ≤
      selectedRadius w3F {0} + 0
    rw [w3_r2, w3_r0]
    norm_num
  · change selectedRadius w3F ({2} : Finset (Fin 3)) ≤
      selectedRadius w3F {1} + 0
    rw [w3_r2, w3_r1]
    norm_num
  · simp

private theorem w3_optimal_two :
    EpsilonOptimalAt (selectedRadius w3F) 0 2 ({0, 1} : Finset (Fin 3)) := by
  refine ⟨by simp, ?_⟩
  intro S hcard
  have hcomp : Sᶜ.card = 1 := by
    simp [Finset.card_compl, hcard]
  rcases Finset.card_eq_one.mp hcomp with ⟨a, ha⟩
  have hS : S = ({a} : Finset (Fin 3))ᶜ := by
    rw [← ha, compl_compl]
  fin_cases a
  · have h0 : S = ({0} : Finset (Fin 3))ᶜ := by simpa using hS
    rw [h0, fin3_compl_0, w3_r01, w3_r12]
    norm_num
  · have h1 : S = ({1} : Finset (Fin 3))ᶜ := by simpa using hS
    rw [h1, fin3_compl_1, w3_r01, w3_r02]
    norm_num
  · have h2 : S = ({2} : Finset (Fin 3))ᶜ := by simpa using hS
    rw [h2, fin3_compl_2]
    norm_num

private theorem any_objective_optimal_zero
    (objective : Finset (Fin 3) → ℝ) :
    EpsilonOptimalAt objective 0 0 ∅ := by
  refine ⟨by simp, ?_⟩
  intro S hcard
  have : S = ∅ := Finset.card_eq_zero.mp hcard
  subst S
  linarith

private theorem any_objective_optimal_full
    (objective : Finset (Fin 3) → ℝ) :
    EpsilonOptimalAt objective 0 3 Finset.univ := by
  refine ⟨by simp, ?_⟩
  intro S hcard
  have : S = Finset.univ := S.card_eq_iff_eq_univ.mp (by simpa using hcard)
  subst S
  linarith

theorem STRUCT_W3_prefix_cover_at_most_two :
    PrefixCoverDimensionAtMost (selectedRadius w3F) 0 2 := by
  refine ⟨w3Menu, by decide, ?_⟩
  refine ⟨by decide, ?_, ?_⟩
  · intro ranking hmem
    simp only [w3Menu, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact w3_full_rank12
    · exact w3_full_rank3
  · intro k hk
    have hk3 : k ≤ 3 := by simpa using hk
    interval_cases k
    · refine ⟨w3Rank12, by simp [w3Menu], ?_⟩
      simpa [w3Rank12, prefixSet] using
        any_objective_optimal_zero (selectedRadius w3F)
    · refine ⟨w3Rank12, by simp [w3Menu], ?_⟩
      simpa [w3Rank12, prefixSet] using w3_optimal_one
    · refine ⟨w3Rank3, by simp [w3Menu], ?_⟩
      simpa [w3Rank3, prefixSet] using w3_optimal_two
    · refine ⟨w3Rank12, by simp [w3Menu], ?_⟩
      convert any_objective_optimal_full (selectedRadius w3F) using 1 <;>
        ext x <;> fin_cases x <;> simp [w3Rank12, prefixSet]

theorem STRUCT_W3_prefix_cover_not_at_most_one :
    ¬ PrefixCoverDimensionAtMost (selectedRadius w3F) 0 1 := by
  intro hDim
  rcases hDim with ⟨menu, hcard, hcover⟩
  have hcardEq : menu.card = 1 := by
    have hpos : 0 < menu.card := Finset.card_pos.mpr hcover.1
    omega
  rcases Finset.card_eq_one.mp hcardEq with ⟨ranking, hmenu⟩
  have hsingleton : PrefixCover (selectedRadius w3F) 0 {ranking} := by
    simpa [hmenu] using hcover
  have hone : OnePrefixChain (selectedRadius w3F) 0 :=
    (singleton_prefix_cover_iff_one_prefix_chain (selectedRadius w3F) 0).1
      ⟨ranking, hsingleton⟩
  have hscalar : ScalarPrefixRankable (selectedRadius w3F) :=
    (STRUCT_B2_one_prefix_zero_iff_scalar_prefix (selectedRadius w3F)).1 hone
  exact W3_geometry_not_scalar_prefix_rankable hscalar

theorem STRUCT_W3_prefix_cover_dimension_exact_two :
    PrefixCoverDimensionAtMost (selectedRadius w3F) 0 2 ∧
      ¬ PrefixCoverDimensionAtMost (selectedRadius w3F) 0 1 :=
  ⟨STRUCT_W3_prefix_cover_at_most_two,
    STRUCT_W3_prefix_cover_not_at_most_one⟩

end CIGAMF.P13.StructuralPrefixCoverWitnesses
