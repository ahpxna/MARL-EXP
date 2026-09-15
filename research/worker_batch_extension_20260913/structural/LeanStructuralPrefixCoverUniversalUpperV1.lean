import Mathlib
import «LeanStructuralOrdinaryChainCharacterizationV1»
import «LeanStructuralUnboundedPrefixCoverFamilyV1»

/-!
# Universal finite upper bound and the staircase linear sandwich

Every budget has an exact optimum.  Extending one optimum at each budget to
one full ranking gives a prefix-cover menu with at most `|I| + 1` rankings.
Combined with the actual support-oscillation staircase family, this proves
linear (Theta in the ground-set size) prefix-menu complexity without claiming
the exact value of the staircase dimension.
-/

namespace CIGAMF.P13.StructuralPrefixCoverUniversalUpper

open CIGAMF.V4.StructuralRankability
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralMinimumTransversalWidth
open CIGAMF.P13.StructuralOrdinaryChainCharacterization
open CIGAMF.P13.StructuralStaircaseFamily
open CIGAMF.P13.StructuralUnboundedPrefixCoverFamily

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem exact_optimum_exists
    (objective : Finset I → ℝ) (k : ℕ)
    (hk : k ≤ Fintype.card I) :
    ∃ S : Finset I, EpsilonOptimalAt objective 0 k S := by
  classical
  let candidates : Finset (Finset I) :=
    Finset.univ.filter fun S : Finset I ↦ S.card = k
  have hCandidates : candidates.Nonempty := by
    have hk' : k ≤ (Finset.univ : Finset I).card := by simpa using hk
    rcases (Finset.univ : Finset I).exists_subset_card_eq hk' with
      ⟨S, -, hSCard⟩
    exact ⟨S, by simp [candidates, hSCard]⟩
  rcases Finset.exists_min_image candidates objective hCandidates with
    ⟨S, hS, hMin⟩
  have hSCard : S.card = k := by simpa [candidates] using hS
  refine ⟨S, hSCard, ?_⟩
  intro T hTCard
  have hT : T ∈ candidates := by simp [candidates, hTCard]
  have := hMin T hT
  linarith

private theorem exact_optimum_extends_to_ranking
    (objective : Finset I → ℝ) (k : ℕ)
    (hk : k ≤ Fintype.card I) :
    ∃ ranking : List I, IsFullRanking ranking ∧
      EpsilonOptimalAt objective 0 k (prefixSet ranking k) := by
  classical
  rcases exact_optimum_exists objective k hk with ⟨S, hOptimal⟩
  have hChain : InclusionChain ({S} : Finset (Finset I)) := by
    intro A hA B hB
    simp only [Finset.mem_singleton] at hA hB
    subst A
    subst B
    exact Or.inl (Finset.Subset.rfl)
  rcases finite_inclusion_chain_extends_to_full_ranking ({S} : Finset (Finset I))
      hChain with ⟨ranking, hFull, hPrefix⟩
  refine ⟨ranking, hFull, ?_⟩
  have hRealize : prefixSet ranking S.card = S := hPrefix S (by simp)
  have hSCard : S.card = k := hOptimal.1
  rw [← hSCard, hRealize]
  simpa [hSCard] using hOptimal

/-- For every finite objective, one exact-optimum ranking per budget gives a
prefix cover of size at most `|I| + 1`. -/
theorem STRUCT_UNIVERSAL_prefix_cover_at_most_card_add_one
    (objective : Finset I → ℝ) :
    PrefixCoverDimensionAtMost objective 0 (Fintype.card I + 1) := by
  classical
  let Budget := Fin (Fintype.card I + 1)
  have hRank : ∀ b : Budget,
      ∃ ranking : List I, IsFullRanking ranking ∧
        EpsilonOptimalAt objective 0 b.val (prefixSet ranking b.val) := by
    intro b
    exact exact_optimum_extends_to_ranking objective b.val (by omega)
  choose ranking hRanking using hRank
  let menu : Finset (List I) := (Finset.univ : Finset Budget).image ranking
  refine ⟨menu, ?_, ?_⟩
  · calc
      menu.card ≤ (Finset.univ : Finset Budget).card := Finset.card_image_le
      _ = Fintype.card I + 1 := by simp [Budget]
  · refine ⟨?_, ?_, ?_⟩
    · exact Finset.image_nonempty.mpr Finset.univ_nonempty
    · intro candidate hCandidate
      rcases Finset.mem_image.mp hCandidate with ⟨b, -, rfl⟩
      exact (hRanking b).1
    · intro k hk
      let b : Budget := ⟨k, by omega⟩
      refine ⟨ranking b, Finset.mem_image.mpr ⟨b, by simp, rfl⟩, ?_⟩
      exact (hRanking b).2

/-- Numerical version: the minimum prefix-cover value is universally at most
the number of budget layers. -/
theorem STRUCT_UNIVERSAL_prefix_dimension_value_le_card_add_one
    (objective : Finset I → ℝ) :
    prefixDimensionValue objective 0 ≤ Fintype.card I + 1 := by
  unfold prefixDimensionValue
  exact Nat.sInf_le
    (STRUCT_UNIVERSAL_prefix_cover_at_most_card_add_one objective)

theorem staircase_ground_card (r : ℕ) :
    Fintype.card (StairRel r) = 2 * r := by
  simp [StairRel, Nat.mul_comm]

/-- The staircase family has a linear lower and upper bound:
`r ≤ chi_prefix(F_r,0) ≤ 2r+1`.  Since its ground set has `2r` elements, this
is the promised Theta(|I|) prefix-menu-complexity statement.  No exact
equality is asserted. -/
theorem STRUCT_UNBOUNDED_staircase_linear_sandwich {r : ℕ} (hr : 0 < r) :
    r ≤ prefixDimensionValue
          (selectedRadius (staircaseF (r := r))) 0 ∧
      prefixDimensionValue
          (selectedRadius (staircaseF (r := r))) 0 ≤ 2 * r + 1 := by
  let objective : Finset (StairRel r) → ℝ :=
    selectedRadius (staircaseF (r := r))
  change r ≤ prefixDimensionValue objective 0 ∧
    prefixDimensionValue objective 0 ≤ 2 * r + 1
  have hUpperPredicate :
      PrefixCoverDimensionAtMost objective 0 (2 * r + 1) := by
    have h := STRUCT_UNIVERSAL_prefix_cover_at_most_card_add_one objective
    rw [staircase_ground_card] at h
    exact h
  have hFeasible :
      {K : ℕ | PrefixCoverDimensionAtMost objective 0 K}.Nonempty :=
    ⟨2 * r + 1, hUpperPredicate⟩
  have hMinFeasible :
      PrefixCoverDimensionAtMost objective 0
        (prefixDimensionValue objective 0) := by
    exact Nat.sInf_mem hFeasible
  constructor
  · by_contra hLower
    have hSmall : prefixDimensionValue objective 0 ≤ r - 1 := by omega
    rcases hMinFeasible with ⟨menu, hMenuCard, hCover⟩
    have hForbidden : PrefixCoverDimensionAtMost objective 0 (r - 1) :=
      ⟨menu, hMenuCard.trans hSmall, hCover⟩
    exact STRUCT_UNBOUNDED_staircase_prefix_dimension_ge hr hForbidden
  · unfold prefixDimensionValue
    exact Nat.sInf_le hUpperPredicate

/-- Discoverable concrete specialization of the parametric theorem.  This is
a twelve-relation (`StairRel 6`) `chi_prefix ≥ 6` result; it is deliberately
not mislabeled as a Fin-8 witness. -/
theorem STRUCT_staircase_r6_not_at_most_five :
    ¬ PrefixCoverDimensionAtMost
      (selectedRadius (staircaseF (r := 6))) 0 5 := by
  exact STRUCT_UNBOUNDED_staircase_prefix_dimension_ge (r := 6) (by norm_num)

end CIGAMF.P13.StructuralPrefixCoverUniversalUpper
