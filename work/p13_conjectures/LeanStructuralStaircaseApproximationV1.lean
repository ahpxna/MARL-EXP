import «LeanStructuralStaircaseExactPrefixCoverV1»

/-! A single ranking is within 1/2 of optimum at every budget in the entire
staircase family. After total-component-radius normalization the error is
1/(2r). Thus exact unbounded prefix complexity need not remain robust. -/
namespace CIGAMF.P13.StructuralStaircaseApproximation
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralStaircaseFamily
open CIGAMF.P13.StructuralStaircaseUnbounded
open CIGAMF.P13.StructuralStaircaseExactPrefixCover
open CIGAMF.P13.StructuralOrdinaryChainCharacterization
open CIGAMF.P13.StructuralMinimumTransversalWidth
noncomputable section

lemma low_subset_negative {r : ℕ} (k : Fin r) :
    lowSelected k ⊆ negativeUniverse := by
  intro j hj
  simp only [negativeUniverse,mem_filter,mem_univ,true_and]
  exact lowSelected_all_negative k j hj

theorem negative_first_ranking_exists (r : ℕ) :
    ∃ ranking : List (StairRel r), IsFullRanking ranking ∧
      prefixSet ranking r = negativeUniverse ∧
      ∀ k : Fin r, prefixSet ranking k.val = lowSelected k := by
  let chain : Finset (Finset (StairRel r)) := insert negativeUniverse (lowChain r)
  have hchain : InclusionChain chain := by
    intro A hA B hB
    rcases mem_insert.mp hA with rfl | hA
    · rcases mem_insert.mp hB with rfl | hB
      · exact Or.inl Subset.rfl
      · obtain ⟨k,hk,rfl⟩ := mem_image.mp hB
        exact Or.inr (low_subset_negative k)
    · rcases mem_insert.mp hB with rfl | hB
      · obtain ⟨k,hk,rfl⟩ := mem_image.mp hA
        exact Or.inl (low_subset_negative k)
      · exact lowChain_inclusionChain A hA B hB
  obtain ⟨ranking,hfull,hprefix⟩ := finite_inclusion_chain_extends_to_full_ranking chain hchain
  refine ⟨ranking,hfull,?_,?_⟩
  · simpa only [negativeUniverse_card] using hprefix negativeUniverse (mem_insert_self _ _)
  · intro k
    have hk : lowSelected k ∈ chain := mem_insert_of_mem (mem_image.mpr ⟨k,mem_univ _,rfl⟩)
    simpa only [lowSelected_card] using hprefix (lowSelected k) hk

theorem radius_le_half_after_negatives {r : ℕ} (S : Finset (StairRel r))
    (hS : negativeUniverse ⊆ S) : selectedRadius staircaseF S ≤ 1/2 := by
  have hneg (i : Fin r) : negativeAt Sᶜ i = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    have h := mem_filter.mp hj
    have hjS : j ∈ S := hS (by simp [negativeUniverse,h.2.1])
    exact (mem_compl.mp h.1) hjS
  have hbounds (a : StairAction r) :
      0 ≤ sumComponent Sᶜ staircaseF a ∧ sumComponent Sᶜ staircaseF a ≤ 1 := by
    cases a with
    | none => simp [sumComponent,staircaseF]
    | some i => rw [staircase_sum_formula,hneg]; simp; split <;> norm_num
  have hmax := maxVal_le (sumComponent Sᶜ staircaseF) (fun a => (hbounds a).2)
  have hmin := le_minVal (sumComponent Sᶜ staircaseF) (fun a => (hbounds a).1)
  unfold selectedRadius supportOsc osc
  linarith

lemma prefix_mono {I : Type*} [DecidableEq I] (ranking : List I) {k l : ℕ}
    (hkl : k ≤ l) : prefixSet ranking k ⊆ prefixSet ranking l := by
  intro x hx
  have hp : ranking.take k <+: ranking.take l := List.take_prefix_take_left hkl
  have hx' : x ∈ ranking.take k := by simpa [prefixSet] using hx
  simpa [prefixSet] using hp.subset hx'

/-- Uniform in r, with an actual support-radius objective and a full ranking. -/
theorem one_ranking_half (r : ℕ) :
    OnePrefixChain (selectedRadius (@staircaseF r)) (1/2) := by
  obtain ⟨ranking,hfull,hneg,hlow⟩ := negative_first_ranking_exists r
  refine ⟨ranking,hfull,?_⟩
  intro k hk
  refine ⟨CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full ranking hfull k hk,?_⟩
  intro T hT
  by_cases hkr : k < r
  · let k' : Fin r := ⟨k,hkr⟩
    have hp := hlow k'
    have ho := (lowSelected_exact_optimal k').2 T hT
    rw [hp]
    linarith
  · have hcontains : negativeUniverse ⊆ prefixSet ranking k := by
      rw [← hneg]; exact prefix_mono ranking (by omega)
    have hradius := radius_le_half_after_negatives _ hcontains
    have hnonneg : 0 ≤ selectedRadius staircaseF T := by
      unfold selectedRadius supportOsc
      exact div_nonneg (osc_nonneg _) (by norm_num)
    linarith

theorem one_ranking_normalized (r : ℕ) (hr : 0 < r) :
    OnePrefixChain (fun S => selectedRadius (@staircaseF r) S / r) (1/(2*(r:ℝ))) := by
  obtain ⟨ranking,hfull,hcover⟩ := one_ranking_half r
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  refine ⟨ranking,hfull,?_⟩
  intro k hk
  refine ⟨(hcover k hk).1,?_⟩
  intro T hT
  have hh := div_le_div_of_nonneg_right ((hcover k hk).2 T hT) hr'.le
  calc
    _ ≤ (selectedRadius staircaseF T + 1/2) / (r:ℝ) := hh
    _ = selectedRadius staircaseF T / (r:ℝ) + 1/(2*(r:ℝ)) := by ring

#print axioms negative_first_ranking_exists
#print axioms radius_le_half_after_negatives
#print axioms one_ranking_half
#print axioms one_ranking_normalized
end
end CIGAMF.P13.StructuralStaircaseApproximation
