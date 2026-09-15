import «LeanStructuralUnbalancedToleranceUpperV1»
import Mathlib.Data.Fin.Tuple.Sort

/-! Reindexing transports the actual radius objective and complete ranking
menus. Thus sorting radii imposes no restriction on the original components. -/
namespace CIGAMF.P13.StructuralRadiusReindex
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralUnbalancedToleranceUpper
noncomputable section
variable {I J Ω : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype Ω] [Nonempty Ω]

lemma radius_reindex (e : J ≃ I) (f : I → Ω → ℝ) (S : Finset J) :
    selectedRadius (fun j => f (e j)) S = selectedRadius f (S.map e.toEmbedding) := by
  have hc : (Sᶜ).map e.toEmbedding = (S.map e.toEmbedding)ᶜ := by
    ext i
    simp only [mem_map,mem_compl,Function.Embedding.coeFn_mk,Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨j,hj,rfl⟩ ⟨k,hk,he⟩
      exact hj ((e.injective he) ▸ hk)
    · intro hi
      refine ⟨e.symm i,?_,e.apply_symm_apply i⟩
      intro hj
      exact hi ⟨e.symm i,hj,e.apply_symm_apply i⟩
  have hs : sumComponent Sᶜ (fun j => f (e j)) = sumComponent ((S.map e.toEmbedding)ᶜ) f := by
    funext x
    rw [← hc]
    simp [sumComponent]
  unfold selectedRadius supportOsc
  rw [hs]

lemma full_map (e : J ≃ I) (r : List J) (hr : IsFullRanking r) : IsFullRanking (r.map e) := by
  refine ⟨hr.1.map e.injective,?_⟩
  ext i
  simp only [List.mem_toFinset,List.mem_map,mem_univ,iff_true]
  have hmem : e.symm i ∈ r.toFinset := by rw [hr.2];simp
  exact ⟨e.symm i,List.mem_toFinset.mp hmem,e.apply_symm_apply i⟩

lemma prefix_map (e : J ≃ I) (r : List J) (k : ℕ) :
    prefixSet (r.map e) k = (prefixSet r k).map e.toEmbedding := by
  unfold prefixSet
  rw [← List.map_take]
  ext i
  simp only [List.mem_toFinset,List.mem_map,mem_map,Equiv.coe_toEmbedding]

theorem cover_reindex (e : J ≃ I) (f : I → Ω → ℝ) (eps : ℝ) (K : ℕ)
    (h : PrefixCoverDimensionAtMost (selectedRadius (fun j => f (e j))) eps K) :
    PrefixCoverDimensionAtMost (selectedRadius f) eps K := by
  obtain ⟨menu,hcard,hne,hfull,hcover⟩ := h
  refine ⟨menu.image (List.map e),card_image_le.trans hcard,image_nonempty.mpr hne,?_,?_⟩
  · intro r hr
    obtain ⟨r0,hm,rfl⟩ := mem_image.mp hr
    exact full_map e r0 (hfull r0 hm)
  · intro k hk
    obtain ⟨r,hr,hopt⟩ := hcover k (by rwa [Fintype.card_congr e])
    refine ⟨r.map e,mem_image.mpr ⟨r,hr,rfl⟩,?_,?_⟩
    · rw [prefix_map,card_map];exact hopt.1
    · intro T hT
      have hmap : (T.map e.symm.toEmbedding).map e.toEmbedding=T := by ext i;simp
      have ho := hopt.2 (T.map e.symm.toEmbedding) (by simpa using hT)
      rw [radius_reindex,radius_reindex,hmap,← prefix_map] at ho
      exact ho

/-- No balance and no pre-existing order on component radii is required. -/
theorem unbalanced_upper (f : I → Ω → ℝ) (c : I → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hf : ∀ i, osc (f i)/2 ≤ c i)
    (eps : ℝ) (heps : 0 < eps) :
    PrefixCoverDimensionAtMost (selectedRadius f) eps (⌊(2*∑ i,c i)/eps⌋₊+1) := by
  let e0 : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let p := Tuple.sort (fun j => c (e0 j))
  let e : Fin (Fintype.card I) ≃ I := p.trans e0
  have hm : Monotone (fun j => c (e j)) := Tuple.monotone_sort (fun j => c (e0 j))
  have hh := sorted_unbalanced_upper (fun j => f (e j)) (fun j => c (e j)) hm
    (fun j => hc0 (e j)) (fun j => hf (e j)) eps heps
  have hsum : (∑ j,c (e j))=∑ i,c i := Equiv.sum_comp e c
  rw [hsum] at hh
  exact cover_reindex e f eps _ hh

/-- Choosing each c_i to be its actual component radius gives the intrinsic
normalization, with a dimension-free 2/eps bound whenever their sum is one. -/
theorem intrinsic_upper (f : I → Ω → ℝ) (eps : ℝ) (heps : 0 < eps) :
    PrefixCoverDimensionAtMost (selectedRadius f) eps
      (⌊(2*∑ i,osc (f i)/2)/eps⌋₊+1) := by
  apply unbalanced_upper f (fun i => osc (f i)/2) _ (fun _ => le_rfl) eps heps
  intro i
  exact div_nonneg (osc_nonneg _) (by norm_num)

#print axioms radius_reindex
#print axioms cover_reindex
#print axioms unbalanced_upper
#print axioms intrinsic_upper
end
end CIGAMF.P13.StructuralRadiusReindex
