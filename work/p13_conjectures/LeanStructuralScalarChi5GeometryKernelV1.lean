import «LeanStructuralScalarChi5KernelV1»

/-! The complete support-geometric chi >= 5 witness, using kernel-checked
finite arithmetic rather than the native_decide facts of the original module.
The final theorem is audited, not only the replacement arithmetic lemmas. -/
namespace CIGAMF.P13.StructuralScalarChi5GeometryKernel
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralGeometryWitnesses
open CIGAMF.V4.StructuralRankability CIGAMF.V6.FunctionalRanking
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralScalarChi5Witness
open CIGAMF.P13.StructuralScalarChi5Kernel

private theorem abs_le_of_eps_optimal
    (S target : Finset (Fin 7)) (k threshold : ℕ)
    (hS : EpsilonOptimalAt (selectedRadius scalarF7) 0 k S)
    (hTargetCard : target.card = k)
    (hTargetAbs : complementAbs7 target = threshold) :
    complementAbs7 S ≤ threshold := by
  have hle := hS.2 target hTargetCard
  rw [scalar_selectedRadius_formula, scalar_selectedRadius_formula,
    hTargetAbs] at hle
  norm_num at hle
  have hcast : (complementAbs7 S : ℝ) ≤ (threshold : ℝ) := by
    linarith
  exact_mod_cast hcast

theorem unique_optimal_one (S : Finset (Fin 7))
    (hS : EpsilonOptimalAt (selectedRadius scalarF7) 0 1 S) :
    S = opt1 := by
  apply unique_abs1_kernel S hS.1
  exact abs_le_of_eps_optimal S opt1 1 1 hS (by decide) opt1_abs_kernel

theorem unique_optimal_two (S : Finset (Fin 7))
    (hS : EpsilonOptimalAt (selectedRadius scalarF7) 0 2 S) :
    S = opt2 := by
  apply unique_abs2_kernel S hS.1
  exact abs_le_of_eps_optimal S opt2 2 0 hS (by decide) opt2_abs_kernel

theorem unique_optimal_three (S : Finset (Fin 7))
    (hS : EpsilonOptimalAt (selectedRadius scalarF7) 0 3 S) :
    S = opt3 := by
  apply unique_abs3_kernel S hS.1
  exact abs_le_of_eps_optimal S opt3 3 1 hS (by decide) opt3_abs_kernel

theorem unique_optimal_four (S : Finset (Fin 7))
    (hS : EpsilonOptimalAt (selectedRadius scalarF7) 0 4 S) :
    S = opt4 := by
  apply unique_abs4_kernel S hS.1
  exact abs_le_of_eps_optimal S opt4 4 2 hS (by decide) opt4_abs_kernel

theorem unique_optimal_five (S : Finset (Fin 7))
    (hS : EpsilonOptimalAt (selectedRadius scalarF7) 0 5 S) :
    S = opt5 := by
  apply unique_abs5_kernel S hS.1
  exact abs_le_of_eps_optimal S opt5 5 0 hS (by decide) opt5_abs_kernel

private theorem prefixSet_mono
    (ranking : List (Fin 7)) {k l : ℕ} (hkl : k ≤ l) :
    prefixSet ranking k ⊆ prefixSet ranking l := by
  intro x hx
  have hp : ranking.take k <+: ranking.take l :=
    List.take_prefix_take_left hkl
  have hxList : x ∈ ranking.take k := by
    simpa [prefixSet] using hx
  have : x ∈ ranking.take l := hp.subset hxList
  simpa [prefixSet] using this

private theorem rankings_distinct_of_incomparable
    (r s : List (Fin 7)) {k l : ℕ} (hkl : k ≤ l)
    (A B : Finset (Fin 7))
    (hr : prefixSet r k = A) (hs : prefixSet s l = B)
    (hnot : ¬ A ⊆ B) : r ≠ s := by
  intro hrs
  subst s
  exact hnot (by simpa [hr, hs] using prefixSet_mono r hkl)

/-- Five forced optimal prefixes are pairwise incomparable, so four rankings
cannot cover all budgets. -/
theorem STRUCT_SCALAR_CHI5_prefix_cover_not_at_most_four :
    ¬ PrefixCoverDimensionAtMost (selectedRadius scalarF7) 0 4 := by
  intro hDim
  rcases hDim with ⟨menu, hMenuCard, hCover⟩
  rcases hCover.2.2 1 (by norm_num) with ⟨r1, hr1, ho1⟩
  rcases hCover.2.2 2 (by norm_num) with ⟨r2, hr2, ho2⟩
  rcases hCover.2.2 3 (by norm_num) with ⟨r3, hr3, ho3⟩
  rcases hCover.2.2 4 (by norm_num) with ⟨r4, hr4, ho4⟩
  rcases hCover.2.2 5 (by norm_num) with ⟨r5, hr5, ho5⟩
  have hp1 := unique_optimal_one _ ho1
  have hp2 := unique_optimal_two _ ho2
  have hp3 := unique_optimal_three _ ho3
  have hp4 := unique_optimal_four _ ho4
  have hp5 := unique_optimal_five _ ho5
  have h12 : r1 ≠ r2 := rankings_distinct_of_incomparable r1 r2 (by omega)
    opt1 opt2 hp1 hp2 (by decide)
  have h13 : r1 ≠ r3 := rankings_distinct_of_incomparable r1 r3 (by omega)
    opt1 opt3 hp1 hp3 (by decide)
  have h14 : r1 ≠ r4 := rankings_distinct_of_incomparable r1 r4 (by omega)
    opt1 opt4 hp1 hp4 (by decide)
  have h15 : r1 ≠ r5 := rankings_distinct_of_incomparable r1 r5 (by omega)
    opt1 opt5 hp1 hp5 (by decide)
  have h23 : r2 ≠ r3 := rankings_distinct_of_incomparable r2 r3 (by omega)
    opt2 opt3 hp2 hp3 (by decide)
  have h24 : r2 ≠ r4 := rankings_distinct_of_incomparable r2 r4 (by omega)
    opt2 opt4 hp2 hp4 (by decide)
  have h25 : r2 ≠ r5 := rankings_distinct_of_incomparable r2 r5 (by omega)
    opt2 opt5 hp2 hp5 (by decide)
  have h34 : r3 ≠ r4 := rankings_distinct_of_incomparable r3 r4 (by omega)
    opt3 opt4 hp3 hp4 (by decide)
  have h35 : r3 ≠ r5 := rankings_distinct_of_incomparable r3 r5 (by omega)
    opt3 opt5 hp3 hp5 (by decide)
  have h45 : r4 ≠ r5 := rankings_distinct_of_incomparable r4 r5 (by omega)
    opt4 opt5 hp4 hp5 (by decide)
  have hfive :
      ({r1, r2, r3, r4, r5} : Finset (List (Fin 7))).card = 5 := by
    simp [h12, h13, h14, h15, h23, h24, h25, h34, h35, h45]
  have hsubset :
      ({r1, r2, r3, r4, r5} : Finset (List (Fin 7))) ⊆ menu := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hr1
    · exact hr2
    · exact hr3
    · exact hr4
    · exact hr5
  have hcardLower := Finset.card_le_card hsubset
  rw [hfive] at hcardLower
  omega

#print axioms opt1_abs_kernel
#print axioms unique_abs1_kernel
#print axioms opt2_abs_kernel
#print axioms unique_abs2_kernel
#print axioms opt3_abs_kernel
#print axioms unique_abs3_kernel
#print axioms opt4_abs_kernel
#print axioms unique_abs4_kernel
#print axioms opt5_abs_kernel
#print axioms unique_abs5_kernel
#print axioms STRUCT_SCALAR_CHI5_prefix_cover_not_at_most_four

end CIGAMF.P13.StructuralScalarChi5GeometryKernel
