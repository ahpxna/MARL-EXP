import «LeanStructuralActualChi4WitnessV1»

/-!
# Kernel-checked replacement for the four `native_decide` steps of the chi>=4 witness

`LeanStructuralActualChi4WitnessV1` proves four subset-enumeration facts by
`native_decide`, a tactic this project rejects as a trust hole: it compiles the
proposition to machine code, runs it, and records the answer through the axiom
`Lean.ofReduceBool`.  Its conclusion
`STRUCT_ACTUAL_CHI4_prefix_cover_not_at_most_three` is therefore a COMPILED
ARTIFACT, not PROVED.

Nothing is deleted.  The four facts are pure combinatorics on `Finset (Fin 6)`
-- they mention neither `chi4F` nor `selectedRadius` -- so they are re-proved
here by kernel `decide`, and the short derivation that depends on them is
repeated verbatim.  Every other step of the original was already kernel
`decide`, `norm_num` or `omega`.

Scale of the kernel work: `Finset (Fin 6)` has 64 elements; each is tested for
cardinality and then against at most 20 explicit subsets.  That is bounded by
64*20 = 1280 decidable equalities on subsets of a six-element type, not a case
explosion.  Each enumeration is a separate theorem so that a failure localises.

The real-valued facts are untouched: the `@[simp]` radius evaluations of the
original module are reused through the simp set, exactly as the original does,
and the final theorem here is proved from the same `chi4F`.
-/

namespace CIGAMF.P13.StructuralActualChi4Kernel

open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.StructuralGeometryWitnesses
open CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralPrefixCoverChi3Witness
open CIGAMF.P13.StructuralActualChi4Witness

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## The four subset enumerations, kernel-checked -/

theorem fin6_card2_cases_kernel :
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
  decide

theorem fin6_card3_cases_kernel :
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
  decide

theorem fin6_card4_cases_kernel :
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
  decide

theorem fin6_card5_cases_kernel :
    ∀ S : Finset (Fin 6), S.card = 5 →
      S = ({0, 1, 2, 3, 4} : Finset (Fin 6)) ∨
      S = ({0, 1, 2, 3, 5} : Finset (Fin 6)) ∨
      S = ({0, 1, 2, 4, 5} : Finset (Fin 6)) ∨
      S = ({0, 1, 3, 4, 5} : Finset (Fin 6)) ∨
      S = ({0, 2, 3, 4, 5} : Finset (Fin 6)) ∨
      S = ({1, 2, 3, 4, 5} : Finset (Fin 6)) := by
  decide

/-! ## The four unique budget optima, re-derived from the kernel enumerations

The `norm_num` steps close each impossible branch using the `@[simp]` radius
evaluations of the original module, which are real-number facts proved there
without `native_decide`. -/

theorem chi4_unique_optimal_two_kernel
    (S : Finset (Fin 6))
    (hS : EpsilonOptimalAt (selectedRadius chi4F) 0 2 S) :
    S = ({0, 5} : Finset (Fin 6)) := by
  have hle := hS.2 ({0, 5} : Finset (Fin 6)) (by decide)
  rcases fin6_card2_cases_kernel S hS.1 with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst S
  all_goals first | exact rfl | norm_num at hle

theorem chi4_unique_optimal_three_kernel
    (S : Finset (Fin 6))
    (hS : EpsilonOptimalAt (selectedRadius chi4F) 0 3 S) :
    S = ({0, 1, 3} : Finset (Fin 6)) := by
  have hle := hS.2 ({0, 1, 3} : Finset (Fin 6)) (by decide)
  rcases fin6_card3_cases_kernel S hS.1 with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst S
  all_goals first | exact rfl | norm_num at hle

theorem chi4_unique_optimal_four_kernel
    (S : Finset (Fin 6))
    (hS : EpsilonOptimalAt (selectedRadius chi4F) 0 4 S) :
    S = ({0, 2, 3, 4} : Finset (Fin 6)) := by
  have hle := hS.2 ({0, 2, 3, 4} : Finset (Fin 6)) (by decide)
  rcases fin6_card4_cases_kernel S hS.1 with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst S
  all_goals first | exact rfl | norm_num at hle

theorem chi4_unique_optimal_five_kernel
    (S : Finset (Fin 6))
    (hS : EpsilonOptimalAt (selectedRadius chi4F) 0 5 S) :
    S = ({1, 2, 3, 4, 5} : Finset (Fin 6)) := by
  have hle := hS.2 ({1, 2, 3, 4, 5} : Finset (Fin 6)) (by decide)
  rcases fin6_card5_cases_kernel S hS.1 with h | h | h | h | h | h <;> subst S
  all_goals first | exact rfl | norm_num at hle

/-! ## Prefix monotonicity and the conclusion -/

theorem prefixSet_mono_kernel
    (ranking : List (Fin 6)) {k l : ℕ} (hkl : k ≤ l) :
    prefixSet ranking k ⊆ prefixSet ranking l := by
  intro x hx
  have hp : ranking.take k <+: ranking.take l := List.take_prefix_take_left hkl
  have hxList : x ∈ ranking.take k := by simpa [prefixSet] using hx
  have hxl : x ∈ ranking.take l := hp.subset hxList
  simpa [prefixSet] using hxl

/-- The same statement as the original module's conclusion, now with no
`Lean.ofReduceBool` anywhere in its dependency set. -/
theorem STRUCT_ACTUAL_CHI4_prefix_cover_not_at_most_three_kernel :
    ¬ PrefixCoverDimensionAtMost (selectedRadius chi4F) 0 3 := by
  intro hDim
  rcases hDim with ⟨menu, hMenuCard, hCover⟩
  rcases hCover.2.2 2 (by norm_num) with ⟨r2, hr2, hopt2⟩
  rcases hCover.2.2 3 (by norm_num) with ⟨r3, hr3, hopt3⟩
  rcases hCover.2.2 4 (by norm_num) with ⟨r4, hr4, hopt4⟩
  rcases hCover.2.2 5 (by norm_num) with ⟨r5, hr5, hopt5⟩
  have hp2 := chi4_unique_optimal_two_kernel _ hopt2
  have hp3 := chi4_unique_optimal_three_kernel _ hopt3
  have hp4 := chi4_unique_optimal_four_kernel _ hopt4
  have hp5 := chi4_unique_optimal_five_kernel _ hopt5
  have h23 : r2 ≠ r3 := by
    intro h; subst r3
    have hsub := prefixSet_mono_kernel r2 (show 2 ≤ 3 by omega)
    rw [hp2, hp3] at hsub
    exact (by decide : ¬(({0, 5} : Finset (Fin 6)) ⊆ {0, 1, 3})) hsub
  have h24 : r2 ≠ r4 := by
    intro h; subst r4
    have hsub := prefixSet_mono_kernel r2 (show 2 ≤ 4 by omega)
    rw [hp2, hp4] at hsub
    exact (by decide : ¬(({0, 5} : Finset (Fin 6)) ⊆ {0, 2, 3, 4})) hsub
  have h25 : r2 ≠ r5 := by
    intro h; subst r5
    have hsub := prefixSet_mono_kernel r2 (show 2 ≤ 5 by omega)
    rw [hp2, hp5] at hsub
    exact (by decide : ¬(({0, 5} : Finset (Fin 6)) ⊆ {1, 2, 3, 4, 5})) hsub
  have h34 : r3 ≠ r4 := by
    intro h; subst r4
    have hsub := prefixSet_mono_kernel r3 (show 3 ≤ 4 by omega)
    rw [hp3, hp4] at hsub
    exact (by decide : ¬(({0, 1, 3} : Finset (Fin 6)) ⊆ {0, 2, 3, 4})) hsub
  have h35 : r3 ≠ r5 := by
    intro h; subst r5
    have hsub := prefixSet_mono_kernel r3 (show 3 ≤ 5 by omega)
    rw [hp3, hp5] at hsub
    exact (by decide : ¬(({0, 1, 3} : Finset (Fin 6)) ⊆ {1, 2, 3, 4, 5})) hsub
  have h45 : r4 ≠ r5 := by
    intro h; subst r5
    have hsub := prefixSet_mono_kernel r4 (show 4 ≤ 5 by omega)
    rw [hp4, hp5] at hsub
    exact (by decide : ¬(({0, 2, 3, 4} : Finset (Fin 6)) ⊆ {1, 2, 3, 4, 5})) hsub
  have hfour : ({r2, r3, r4, r5} : Finset (List (Fin 6))).card = 4 := by
    simp [h23, h24, h25, h34, h35, h45]
  have hsubset : ({r2, r3, r4, r5} : Finset (List (Fin 6))) ⊆ menu := by
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

#print axioms fin6_card2_cases_kernel
#print axioms fin6_card3_cases_kernel
#print axioms fin6_card4_cases_kernel
#print axioms fin6_card5_cases_kernel
#print axioms chi4_unique_optimal_two_kernel
#print axioms chi4_unique_optimal_three_kernel
#print axioms chi4_unique_optimal_four_kernel
#print axioms chi4_unique_optimal_five_kernel
#print axioms STRUCT_ACTUAL_CHI4_prefix_cover_not_at_most_three_kernel

end CIGAMF.P13.StructuralActualChi4Kernel
