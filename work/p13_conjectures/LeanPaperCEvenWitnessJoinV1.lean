import «LeanPaperCFam13V1»
import «LeanPaperCEvenResolveV1»
import «LeanPaperCLawRelabelV1»

/-!
DRAFT SOURCE — no compile claim. Concrete #13 closure, with no hclass/hvalue premises.
All counts are taken from CFam13/CUniform and the value from CEvenResolve; the final
witness is a law on ALL permutations of the original gFamily, not a menu optimum.
-/
namespace CIGAMF.P13.PaperCEvenWitnessJoin
open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCEven CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCFam13 CIGAMF.P13.PaperCUniform CIGAMF.P13.PaperCEvenResolve
open CIGAMF.P13.PaperCInstantiation CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCRelabel CIGAMF.P13.PaperCLowerZero
open CIGAMF.P13.PaperCLawRelabel CIGAMF.P13.PaperCLawPush

/-- Explicit relabelling: alternating light items are sorted by sign. -/
noncomputable def flatToFamily (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m) : Equiv.Perm (Fin m) where
  toFun i := ⟨if i.val=0 then 0 else if i.val=m-1 then m-1
    else if i.val%2=0 then i.val/2 else (m-2)/2+(i.val+1)/2, by
      have hi := i.isLt; have hp := Nat.even_iff.mp hm
      split_ifs <;> omega⟩
  invFun j := ⟨if j.val=0 then 0 else if j.val=m-1 then m-1
    else if j.val≤(m-2)/2 then 2*j.val else 2*(j.val-(m-2)/2)-1, by
      have hj := j.isLt; have hp := Nat.even_iff.mp hm
      split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext
    have hi := i.isLt; have hp := Nat.even_iff.mp hm
    simp only [Fin.val_mk]
    split_ifs <;> omega
  right_inv j := by
    apply Fin.ext
    have hj := j.isLt; have hp := Nat.even_iff.mp hm
    simp only [Fin.val_mk]
    split_ifs <;> omega

theorem flatToFamily_apply (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m) (i : Fin m) :
    gFamily m (flatToFamily m hm hm4 i) = flatEven m i := by
  have hi := i.isLt; have hp := Nat.even_iff.mp hm
  unfold flatToFamily gFamily gN flatEven flatW
  simp only [Fin.val_mk]
  split_ifs <;> first | rfl | omega

theorem family_position_counts (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m)
    (k : ℕ) (hk : k ≤ m) (w : ℝ) :
    (∑ x : FamIdx m, famQ m x * ∑ p ∈ univ.filter (fun p : Fin m => p.val < k),
      (if flatEven m (basePerm m hm hm4 x p)=w then (1:ℝ) else 0))
      = ((univ.filter (fun i : Fin m => flatEven m i=w)).card:ℝ)*(k:ℝ)/(m:ℝ) := by
  classical
  have hm2 : 1 < m := by omega
  have hmR : (m:ℝ) ≠ 0 := by positivity
  by_cases hk0 : k=0
  · subst k; simp
  by_cases hkm : k=m
  · subst k
    have hcount : ∀ x : FamIdx m,
        (∑ p ∈ univ.filter (fun p : Fin m => p.val < m),
          (if flatEven m (basePerm m hm hm4 x p)=w then (1:ℝ) else 0))
        = ((univ.filter (fun i : Fin m => flatEven m i=w)).card:ℝ) := by
      intro x
      simp only [Fin.isLt, filter_true_of_mem, sum_filter]
      rw [Equiv.sum_comp (basePerm m hm hm4 x)]
      simp
    simp_rw [hcount]
    rw [← sum_mul, famQ_sum m (by omega)]
    field_simp
  have hk1 : 1 ≤ k := by omega
  have hkl : k ≤ m-1 := by omega
  simp_rw [prefix_count_eq m hm hm4 _ k hk]
  change (∑ x : FamIdx m, (1/(2*(m:ℝ))) * cntBelow (famW m x) k w) = _
  rw [fam_avg_eq_uniformMix m k hm2 w]
  by_cases h3 : w=3
  · subst w; rw [uniformMix_heavy m k hm2 hk1 hkl, flatClass_three m hm2]; ring
  by_cases hn3 : w = -3
  · subst w
    rw [← uniformMix_symm m 3 k, uniformMix_heavy m k hm2 hk1 hkl,
      flatClass_neg_three m hm2]; ring
  by_cases h1 : w=1
  · subst w; rw [uniformMix_light m k hm2 hk1 hkl, flatClass_one m hm hm4]; ring
  by_cases hn1 : w = -1
  · subst w
    rw [← uniformMix_symm m 1 k, uniformMix_light m k hm2 hk1 hkl,
      flatClass_neg_one m hm hm4]; ring
  have hf : (univ.filter (fun i : Fin m => flatEven m i=w)) = ∅ := by
    ext i
    simp only [mem_filter,mem_univ,true_and,notMem_empty,iff_false]
    intro hiw
    have hi4 := flatW_mem m i.val
    change flatW m i.val=w at hiw
    rcases hi4 with h | h | h | h <;> simp_all
  rw [hf,card_empty,Nat.cast_zero,zero_mul,zero_div]
  rw [← fam_avg_eq_uniformMix m k hm2 w]
  apply sum_eq_zero
  intro x _
  unfold cntBelow
  have hzero : ∀ i ∈ range k, (if famW m x i=w then (1:ℝ) else 0)=0 := by
    intro i hi
    rcases x with ⟨a,b⟩
    cases a with
    | inl a => cases b <;> simp only [famW] <;>
        have h := insWeight_mem a.val i <;> rcases h with h|h|h|h <;> simp_all
    | inr a => cases b <;> simp only [famW] <;>
        have h := flatW_mem m i <;> rcases h with h|h|h|h <;> simp_all
  simp [sum_congr rfl hzero]

theorem family_class_occupancy (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m)
    (k : ℕ) (hk : k ≤ m) (w : ℝ) :
    (∑ j ∈ univ.filter (fun j : Fin m => flatEven m j=w),
      baseMarg (basePerm m hm hm4) (famQ m) k j)
      = ((univ.filter (fun j : Fin m => flatEven m j=w)).card:ℝ)*((k:ℝ)/(m:ℝ)) := by
  apply hclass_of_position_counts
  simpa only [mul_div_assoc] using family_position_counts m hm hm4 k hk w

theorem family_expected_value (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m)
    (k : ℕ) (hk1 : 1 ≤ k) (hkl : k ≤ m-1) :
    (∑ x : FamIdx m, famQ m x * regret (flatEven m) (basePerm m hm hm4 x) ((m:ℝ)+4) k)
      = 4/((m:ℝ)*((m:ℝ)+4)) := by
  classical
  have hrank : ∀ x : FamIdx m, rankOf (flatEven m) (basePerm m hm hm4 x)=famRanking m x := by
    intro x; funext p; exact basePerm_apply m hm hm4 x p
  unfold regret
  simp_rw [hrank]
  unfold famQ
  rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [Fintype.sum_bool, famRanking, famW, Finset.univ_unique, Finset.sum_singleton]
  rw [Fin.sum_univ_eq_sum_range]
  convert evenMixtureFlipped_value_at_D m (by omega) k hk1 hkl using 1 <;>
    simp only [add_comm,add_left_comm,add_assoc]

/-- Concrete uniform-band witness; no class-count or value hypothesis remains. -/
theorem even_allPerm_witness (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m)
    (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (hbud : ∀ k ∈ budgets, 1 ≤ k ∧ k ≤ m-1) :
    ∃ P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) 0,
      maxRegret P (gFamily m) id ((m:ℝ)+4) budgets hne = 4/((m:ℝ)*((m:ℝ)+4)) := by
  classical
  obtain ⟨hfeas,hval⟩ := witness_of_relabelled (flatEven m) (basePerm m hm hm4) (famQ m)
    (famQ_nonneg m) (famQ_sum m (by omega)) (family_class_occupancy m hm hm4)
    ((m:ℝ)+4) (4/((m:ℝ)*((m:ℝ)+4))) budgets hne
    (fun k hk => family_expected_value m hm hm4 k (hbud k hk).1 (hbud k hk).2)
  exact actual_allPerm_witness_of_menu (flatEven m) (gFamily m)
    (flatToFamily m hm hm4) (flatToFamily_apply m hm hm4)
    _ _ _ 0 _ budgets hne hfeas hval

/-- Sum of absolute weights, derived from the two heavy entries rather than supplied. -/
theorem gFamily_abs_sum (m : ℕ) (hm3 : 3 ≤ m) : ∑ i, |gFamily m i| = (m:ℝ)+4 := by
  classical
  have hh : (heavySet (gFamily m)).card=2 := by
    convert gFamily_heavy_card (m-2) (by omega) using 1 <;> congr 1 <;> omega
  have hpt : ∀ i : Fin m,
      |gFamily m i| = 1+2*(if i∈heavySet (gFamily m) then (1:ℝ) else 0) := by
    intro i
    rcases gFamily_weights m i with h|h|h|h <;>
      simp [mem_heavySet,h]
  simp_rw [hpt]
  rw [sum_add_distrib]
  simp [← mul_sum,hh]

/-- The value is for the complete permutation game, with universal lower bound. -/
theorem even_allPerm_value (m : ℕ) (hm : Even m) (hm4 : 4 ≤ m)
    (budgets : Finset ℕ) (hne : budgets.Nonempty) (h1 : 1∈budgets)
    (hbud : ∀ k∈budgets, 1≤k ∧ k≤m-1) :
    Vm (gFamily m) id ((m:ℝ)+4) 0 budgets hne = 4/((m:ℝ)*((m:ℝ)+4)) := by
  apply Vm_eq_at_zero (by omega) (gFamily m) id (gFamily_abs_sum m (by omega))
    budgets hne h1 (by positivity) (fun k hk => by have := (hbud k hk).2; omega)
  · intro σ i; exact gFamily_weights m (σ i)
  · exact even_allPerm_witness m hm hm4 budgets hne hbud

#print axioms flatToFamily_apply
#print axioms family_class_occupancy
#print axioms family_expected_value
#print axioms even_allPerm_witness
#print axioms even_allPerm_value
end CIGAMF.P13.PaperCEvenWitnessJoin
