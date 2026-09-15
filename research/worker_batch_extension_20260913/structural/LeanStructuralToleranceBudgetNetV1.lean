import «LeanStructuralPrefixCoverUniversalUpperV1»

/-! A quantitative budget net for actual support radius. Uniformly small
component radii make one exact ranking cover a whole interval of budgets.
This upper bound does not assume monotonicity or submodularity of the objective. -/
namespace CIGAMF.P13.StructuralToleranceBudgetNet
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralOrdinaryChainCharacterization
open CIGAMF.P13.StructuralMinimumTransversalWidth
noncomputable section
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]

lemma radius_nested_change (f : I → Ω → ℝ) (S T : Finset I) (hST : S ⊆ T) :
    |selectedRadius f S-selectedRadius f T| ≤ ∑ i ∈ T\S,osc (f i)/2 := by
  have hd : Disjoint (Tᶜ) (T\S) := by
    apply disjoint_left.mpr
    intro i hi hj
    exact (mem_compl.mp hi) (mem_sdiff.mp hj).1
  have hu : Tᶜ ∪ (T\S)=Sᶜ := by
    ext i
    by_cases hs : i ∈ S
    · simp [hs,hST hs]
    · by_cases ht : i ∈ T <;> simp [hs,ht]
  have he : sumComponent Sᶜ f = fun x => sumComponent Tᶜ f x+sumComponent (T\S) f x := by
    funext x
    simp only [sumComponent,← hu,sum_union hd]
  have hb := osc_add_deviation (sumComponent Tᶜ f) (sumComponent (T\S) f)
  rw [← he] at hb
  have hm := BH2_supportOsc_le_modularSpan (T\S) f
  change osc (sumComponent (T\S) f) ≤ ∑ i ∈ T\S,osc (f i) at hm
  simp only [selectedRadius,supportOsc,← sub_div,abs_div,show |(2:ℝ)|=2 by norm_num,← sum_div]
  exact div_le_div_of_nonneg_right (hb.trans hm) (by norm_num)

lemma radius_nested_uniform (f : I → Ω → ℝ) (c : ℝ)
    (hc : ∀ i, osc (f i)/2 ≤ c) (S T : Finset I) (hST : S ⊆ T) :
    |selectedRadius f S-selectedRadius f T| ≤ ((T.card-S.card : ℕ):ℝ)*c := by
  apply (radius_nested_change f S T hST).trans
  calc
    (∑ i ∈ T\S,osc (f i)/2) ≤ ∑ _i ∈ T\S,c := sum_le_sum (fun i _ => hc i)
    _ = ((T.card-S.card : ℕ):ℝ)*c := by simp [card_sdiff_of_subset hST]

/-- Every extension of a k-optimum is 2*c*(l-k)-optimal at budget l. -/
theorem optimal_extension (f : I → Ω → ℝ) (c : ℝ)
    (hc : ∀ i, osc (f i)/2 ≤ c) (S P : Finset I) (hSP : S ⊆ P)
    (hopt : EpsilonOptimalAt (selectedRadius f) 0 S.card S) :
    EpsilonOptimalAt (selectedRadius f) (2*c*((P.card-S.card : ℕ):ℝ)) P.card P := by
  refine ⟨rfl,?_⟩
  intro T hT
  obtain ⟨R,hRT,hR⟩ := T.exists_subset_card_eq (show S.card ≤ T.card by rw [hT];exact card_le_card hSP)
  have hmin := hopt.2 R hR
  have h1 := (abs_le.mp (radius_nested_uniform f c hc S P hSP)).1
  have h2 := (abs_le.mp (radius_nested_uniform f c hc R T hRT)).2
  rw [hT,hR] at h2
  nlinarith

lemma prefix_subset (r : List I) {k l : ℕ} (h : k ≤ l) : prefixSet r k ⊆ prefixSet r l := by
  intro i hi
  have hh : r.take k <+: r.take l := List.take_prefix_take_left h
  exact List.mem_toFinset.mpr (hh.subset (List.mem_toFinset.mp hi))

lemma exact_ranking (f : I → Ω → ℝ) (k : ℕ) (hk : k ≤ Fintype.card I) :
    ∃ r : List I, IsFullRanking r ∧ EpsilonOptimalAt (selectedRadius f) 0 k (prefixSet r k) := by
  let candidates : Finset (Finset I) := univ.filter (fun S => S.card=k)
  have hne : candidates.Nonempty := by
    obtain ⟨S,_,hs⟩ := (univ : Finset I).exists_subset_card_eq (by simpa using hk)
    exact ⟨S,by simp [candidates,hs]⟩
  obtain ⟨S,hs,hmin⟩ := exists_min_image candidates (selectedRadius f) hne
  have hcard : S.card=k := (mem_filter.mp hs).2
  have hchain : InclusionChain ({S} : Finset (Finset I)) := by
    intro A hA B hB
    simp only [mem_singleton] at hA hB
    subst A; subst B; exact Or.inl (Subset.rfl)
  obtain ⟨r,hr,hprefix⟩ := finite_inclusion_chain_extends_to_full_ranking {S} hchain
  have he : prefixSet r k=S := by rw [← hcard];exact hprefix S (by simp)
  refine ⟨r,hr,?_⟩
  rw [he]
  exact ⟨hcard,fun T hT => by simpa using hmin T (by simp [candidates,hT])⟩

/-- Spacing h yields at most floor(m/h)+1 rankings and tolerance 2*c*h.
For normalized balanced components c=O(1/m), taking h proportional to m
makes this bound independent of m at each fixed positive tolerance. -/
theorem budget_net_cover (f : I → Ω → ℝ) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ i, osc (f i)/2 ≤ c) (h : ℕ) (hh : 0 < h) :
    PrefixCoverDimensionAtMost (selectedRadius f) (2*c*h) (Fintype.card I/h+1) := by
  let B := Fin (Fintype.card I/h+1)
  have hex (b : B) : ∃ r : List I, IsFullRanking r ∧
      EpsilonOptimalAt (selectedRadius f) 0 (b.val*h) (prefixSet r (b.val*h)) := by
    apply exact_ranking
    have hb : b.val ≤ Fintype.card I/h := by omega
    exact (Nat.mul_le_mul_right h hb).trans (Nat.div_mul_le_self _ _)
  choose r hr using hex
  let menu : Finset (List I) := univ.image r
  refine ⟨menu,?_,?_,?_,?_⟩
  · exact card_image_le.trans (by simp [B])
  · exact image_nonempty.mpr univ_nonempty
  · intro a ha
    obtain ⟨b,_,rfl⟩ := mem_image.mp ha
    exact (hr b).1
  · intro k hk
    let b : B := ⟨k/h,by have hd : k/h ≤ Fintype.card I/h := Nat.div_le_div_right hk;omega⟩
    have hanchor : b.val*h ≤ k := Nat.div_mul_le_self _ _
    have ha : b.val*h ≤ Fintype.card I := hanchor.trans hk
    have hkcard := CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full (r b) (hr b).1 k hk
    have hacard := CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full (r b) (hr b).1 (b.val*h) ha
    have ho : EpsilonOptimalAt (selectedRadius f) 0
        (prefixSet (r b) (b.val*h)).card (prefixSet (r b) (b.val*h)) := by
      rw [hacard];exact (hr b).2
    have ht := optimal_extension f c hc _ _ (prefix_subset (r b) hanchor) ho
    rw [hkcard,hacard] at ht
    have hrem : k-b.val*h ≤ h := by
      dsimp [b]
      rw [← Nat.mod_eq_sub_div_mul]
      exact (Nat.mod_lt k hh).le
    have heps : 2*c*((k-b.val*h : ℕ):ℝ) ≤ 2*c*h :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hrem) (by positivity)
    refine ⟨r b,mem_image.mpr ⟨b,mem_univ _,rfl⟩,ht.1,?_⟩
    intro T hT
    have hb := ht.2 T hT
    linarith

#print axioms radius_nested_change
#print axioms optimal_extension
#print axioms budget_net_cover
end
end CIGAMF.P13.StructuralToleranceBudgetNet
