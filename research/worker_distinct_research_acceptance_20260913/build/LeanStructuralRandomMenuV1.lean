import «LeanStructuralStaircaseToleranceLowerV1»
import Mathlib

/-! Pointwise menu hit counts, finite randomized lower bound and the
post-randomization adversary on the actual normalized staircase geometry. -/
namespace CIGAMF.P13.StructuralRandomMenu
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralStaircaseFamily
open CIGAMF.P13.StructuralUnboundedPrefixCoverFamily
open CIGAMF.P13.StructuralStaircaseToleranceLower
noncomputable section
attribute [local instance] Classical.propDecidable
variable {r : ℕ}

def Hits (eps : ℝ) (ranking : List (StairRel r)) (t : Fin r) : Prop :=
  EpsilonOptimalAt (fun S => selectedRadius staircaseF S/(r : ℝ)) eps
    (staircaseSelected t).card (prefixSet ranking (staircaseSelected t).card)

lemma prefix_mono (ranking : List (StairRel r)) {k l : ℕ} (h : k ≤ l) :
    prefixSet ranking k ⊆ prefixSet ranking l := by
  intro x hx
  have hp : ranking.take k <+: ranking.take l := List.take_prefix_take_left h
  have hm : x ∈ ranking.take k := by simpa [prefixSet] using hx
  simpa [prefixSet] using hp.subset hm

theorem ranking_hits_at_most_one (hr : 0 < r) (eps : ℝ) (heps : 2*(r:ℝ)*eps<1)
    (ranking : List (StairRel r)) (s t : Fin r)
    (hs : Hits eps ranking s) (ht : Hits eps ranking t) : s=t := by
  have hs' := staircaseSelected_unique_optimal hr s _
    (normalized_epsilon_exact hr eps heps _ _ hs)
  have ht' := staircaseSelected_unique_optimal hr t _
    (normalized_epsilon_exact hr eps heps _ _ ht)
  by_contra hst
  rcases le_total (staircaseSelected s).card (staircaseSelected t).card with h | h
  · apply staircaseSelected_incomparable hst
    rw [← hs',← ht']
    exact prefix_mono ranking h
  · apply staircaseSelected_incomparable (Ne.symm hst)
    rw [← ht',← hs']
    exact prefix_mono ranking h

def hitSet (eps : ℝ) (menu : Finset (List (StairRel r))) : Finset (Fin r) :=
  univ.filter (fun t => ∃ ranking ∈ menu, Hits eps ranking t)

theorem menu_hit_count (hr : 0 < r) (eps : ℝ) (heps : 2*(r:ℝ)*eps<1)
    (menu : Finset (List (StairRel r))) : (hitSet eps menu).card ≤ menu.card := by
  have hex : ∀ t : hitSet eps menu, ∃ ranking ∈ menu, Hits eps ranking t.val := by
    intro t
    simpa only [hitSet,mem_filter,mem_univ,true_and] using t.property
  choose f hfmem hfhit using hex
  have hinj : Function.Injective f := by
    intro s t he
    apply Subtype.ext
    apply ranking_hits_at_most_one hr eps heps (f s) s.val t.val (hfhit s)
    rw [he]; exact hfhit t
  have hc : Fintype.card (hitSet eps menu) ≤ Fintype.card menu :=
    Fintype.card_le_of_injective (fun t => (⟨f t,hfmem t⟩ : menu)) (by
      intro s t he; exact hinj (congrArg Subtype.val he))
  simpa using hc

theorem post_randomization_adversary (hr : 0 < r) (eps : ℝ)
    (heps : 2*(r:ℝ)*eps<1) (menu : Finset (List (StairRel r))) (hm : menu.card<r) :
    ∃ t : Fin r, ∀ ranking ∈ menu, ¬ Hits eps ranking t := by
  have hc := menu_hit_count hr eps heps menu
  have hne : hitSet eps menu ≠ univ := by
    intro h; rw [h] at hc; simp at hc; omega
  have hex : ∃ t, t ∉ hitSet eps menu := by
    by_contra h
    push_neg at h
    apply hne
    ext t
    simp [h t]
  obtain ⟨t,ht⟩ := hex
  refine ⟨t,?_⟩
  simpa [hitSet] using ht

theorem random_menu_lower {Ω : Type*} [Fintype Ω] (hr : 0 < r) (eps delta : ℝ)
    (heps : 2*(r:ℝ)*eps<1) (p : Ω → ℝ) (hp : ∀ o,0 ≤ p o)
    (hpsum : ∑ o,p o=1) (menu : Ω → Finset (List (StairRel r))) (K : ℕ)
    (hK : ∀ o,(menu o).card ≤ K)
    (hs : ∀ t : Fin r, 1-delta ≤ ∑ o, p o*(if t ∈ hitSet eps (menu o) then 1 else 0)) :
    (r:ℝ)*(1-delta) ≤ K := by
  have hlow := Finset.sum_le_sum (fun t (_ : t ∈ (univ : Finset (Fin r))) => hs t)
  have hpoint : ∀ o, (∑ t : Fin r,p o*(if t ∈ hitSet eps (menu o) then 1 else 0)) ≤ p o*K := by
    intro o
    rw [← Finset.mul_sum]
    have hc : ((hitSet eps (menu o)).card : ℝ) ≤ K := by
      exact_mod_cast (menu_hit_count hr eps heps (menu o)).trans (hK o)
    simpa using mul_le_mul_of_nonneg_left hc (hp o)
  have hhigh := Finset.sum_le_sum (fun o (_ : o ∈ (univ : Finset Ω)) => hpoint o)
  rw [← Finset.sum_mul,hpsum,one_mul] at hhigh
  rw [Finset.sum_comm] at hlow
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hlow
  exact hlow.trans hhigh

/-- Uniform K-subsets: exact finite membership count, including K=0. -/
theorem uniform_submenu_count {X : Type*} [DecidableEq X] (S : Finset X)
    (x : X) (hx : x ∈ S) (K : ℕ) (hK : 0 < K) :
    ((S.powersetCard K).filter (fun T => x ∈ T)).card = (S.card-1).choose (K-1) := by
  have h := card_filter_powersetCard_subset ({x}:Finset X) S K
    (singleton_subset_iff.mpr hx) (by simp only [card_singleton]; omega)
  simpa using h

theorem uniform_membership_probability {X : Type*} [DecidableEq X] (S : Finset X)
    (x : X) (hx : x ∈ S) (K : ℕ) (hK : 0 < K) (hKS : K ≤ S.card) :
    (((S.powersetCard K).filter (fun T => x ∈ T)).card : ℝ) /
      (S.powersetCard K).card = (K : ℝ)/S.card := by
  rw [uniform_submenu_count S x hx K hK, card_powersetCard]
  have hS : 0 < S.card := card_pos.mpr ⟨x,hx⟩
  have hc : 0 < S.card.choose K := Nat.choose_pos hKS
  have hn := Nat.add_one_mul_choose_eq (S.card-1) (K-1)
  have hs1 : S.card-1+1=S.card := by omega
  have hk1 : K-1+1=K := by omega
  rw [hs1,hk1] at hn
  have hn' : (S.card : ℝ)*((S.card-1).choose (K-1) : ℝ) =
      (S.card.choose K : ℝ)*K := by exact_mod_cast hn
  apply (div_eq_div_iff (by exact_mod_cast (ne_of_gt hc))
    (by exact_mod_cast (ne_of_gt hS))).mpr
  nlinarith

theorem uniform_submenu_coverage {X : Type*} [DecidableEq X] (S : Finset X)
    (Good : X → Prop) (hcover : ∃ x ∈ S,Good x) (K : ℕ)
    (hK : 0 < K) (hKS : K ≤ S.card) :
    (K : ℝ)/S.card ≤
      (((S.powersetCard K).filter (fun T => ∃ x ∈ T,Good x)).card : ℝ) /
        (S.powersetCard K).card := by
  obtain ⟨x,hx,hg⟩ := hcover
  rw [← uniform_membership_probability S x hx K hK hKS]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (card_le_card (show
      (S.powersetCard K).filter (fun T => x ∈ T) ⊆
      (S.powersetCard K).filter (fun T => ∃ x ∈ T,Good x) from by
    intro T hT
    exact mem_filter.mpr ⟨(mem_filter.mp hT).1,x,(mem_filter.mp hT).2,hg⟩))

open CIGAMF.P13.StructuralStaircaseExactPrefixCover

theorem canonical_menu_card (hr : 0 < r) : (stairMenu r).card=r := by
  apply le_antisymm stairMenu_card_le
  by_contra h
  have hc : (stairMenu r).card ≤ r-1 := by omega
  exact STRUCT_UNBOUNDED_staircase_prefix_dimension_ge hr
    ⟨stairMenu r,hc,stairMenu_prefixCover hr⟩

theorem actual_uniform_submenu_coverage (hr : 0 < r) (eps : ℝ) (he : 0 ≤ eps)
    (K k : ℕ) (hK : 0 < K) (hKr : K ≤ r) (hk : k ≤ Fintype.card (StairRel r)) :
    (K : ℝ)/r ≤
      (((stairMenu r).powersetCard K).filter (fun M => ∃ ranking ∈ M,
        EpsilonOptimalAt (fun S => selectedRadius staircaseF S/(r : ℝ)) eps k
          (prefixSet ranking k))).card / (((stairMenu r).powersetCard K).card : ℝ) := by
  have hcover : ∃ ranking ∈ stairMenu r,
      EpsilonOptimalAt (fun S => selectedRadius staircaseF S/(r : ℝ)) eps k
        (prefixSet ranking k) := by
    obtain ⟨ranking,hm,ho⟩ := (stairMenu_prefixCover hr).2.2 k hk
    refine ⟨ranking,hm,ho.1,?_⟩
    intro T hT
    have h := ho.2 T hT
    have hh := div_le_div_of_nonneg_right (show selectedRadius staircaseF (prefixSet ranking k) ≤
      selectedRadius staircaseF T by linarith) (show (0 : ℝ) ≤ r by positivity)
    linarith
  have h := uniform_submenu_coverage (stairMenu r) _ hcover K hK
    (by rw [canonical_menu_card hr]; exact hKr)
  simpa only [canonical_menu_card hr] using h

#print axioms uniform_membership_probability
#print axioms uniform_submenu_coverage
#print axioms canonical_menu_card
#print axioms actual_uniform_submenu_coverage
#print axioms ranking_hits_at_most_one
#print axioms menu_hit_count
#print axioms post_randomization_adversary
#print axioms random_menu_lower
#print axioms uniform_submenu_count
end
end CIGAMF.P13.StructuralRandomMenu
