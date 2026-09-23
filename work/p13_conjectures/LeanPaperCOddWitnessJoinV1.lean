import «LeanPaperCRearrangeV1»
import «LeanPaperCValueV1»
import «LeanPaperCOmitV1»
import «LeanPaperCLawRelabelV1»

/-!
DRAFT source, not compiled. This joins the existing odd window calculation to an actual
law on all permutations of gFamily. The lower bound is for EVERY uniform-marginal law,
using its uniform omitted item, not just for the constructed cyclic law.
-/
namespace CIGAMF.P13.PaperCOddWitnessJoin
open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCOdd CIGAMF.P13.PaperCRearrange
open CIGAMF.P13.PaperCWindow CIGAMF.P13.PaperCValue CIGAMF.P13.PaperCOmit
open CIGAMF.P13.PaperCPerm CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCValueSet
open CIGAMF.P13.PaperCRelabel CIGAMF.P13.PaperCLawRelabel CIGAMF.P13.PaperCLawPush

noncomputable def oddToFamily (s : ℕ) : Equiv.Perm (Fin (2*s+3)) :=
  permOfCountEq (oddBase (2*s+3)) (gFamily (2*s+3)) (fun w => by
    simpa [Fintype.card_subtype,countVal] using countVal_agree s w)

theorem oddToFamily_apply (s : ℕ) (i : Fin (2*s+3)) :
    gFamily (2*s+3) (oddToFamily s i) = oddBase (2*s+3) i :=
  permOfCountEq_apply _ _ _ i

/-- Prefix of a rotation is precisely the already-verified natural-index window. -/
theorem rotated_prefix_eq_win (m : ℕ) [NeZero m] (a : Fin m) (k : ℕ) (hk : k≤m) :
    prefixSum (rankOf (oddBase m) (cyclicPerm m a)) k = win m a.val k := by
  classical
  unfold prefixSum rankOf cyclicPerm
  rw [sum_filter, Fin.sum_univ_eq_sum_range]
  have hsub : range k ⊆ range m := range_mono hk
  rw [← sum_subset hsub (fun i hi hni => by simp [not_lt.mpr (by simpa using hni)])]
  unfold win
  apply sum_congr rfl
  intro i hi
  have hik : i<k := mem_range.mp hi
  simp only [dif_pos (lt_of_lt_of_le hik hk), if_pos hik, Equiv.addRight_apply,
    oddBase, baseN, Fin.val_add, Nat.add_comm]

theorem rotated_expected_regret (m : ℕ) [NeZero m] (D : ℝ)
    (k : ℕ) (hk : k≤m) :
    (∑ a : Fin m, cyclicLaw m a * regret (oddBase m) (cyclicPerm m a) D k)
      = winValue m k / D := by
  classical
  have hmR : (m:ℝ)≠0 := by exact_mod_cast (NeZero.ne m)
  unfold regret excess cyclicLaw
  simp_rw [rotated_prefix_eq_win m _ k hk]
  rw [show (∑ a : Fin m, 1/(m:ℝ) *
      ((|win m a.val k|-((k%2:ℕ):ℝ))/D))
      = ((∑ a : Fin m, |win m a.val k|)/(m:ℝ)-((k%2:ℕ):ℝ))/D by
        rw [← sum_div, ← mul_sum, sum_sub_distrib]
        simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
        field_simp; ring]
  rw [Fin.sum_univ_eq_sum_range]
  rfl

theorem odd_cyclic_max (s : ℕ) (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (hbud : ∀ k∈budgets, 1≤k ∧ k<2*s+3) (hlast : 2*s+3-1∈budgets) :
    maxRegret (cyclicLaw (2*s+3)) (oddBase (2*s+3)) (cyclicPerm (2*s+3))
      ((2*s+3:ℕ)+4) budgets hne
      = (((2*s+3:ℕ):ℝ)+3)/(((2*s+3:ℕ):ℝ)*(((2*s+3:ℕ):ℝ)+4)) := by
  classical
  have hD : (0:ℝ)<((2*s+3:ℕ):ℝ)+4 := by positivity
  unfold maxRegret
  apply le_antisymm
  · apply sup'_le
    intro k hk
    rw [rotated_expected_regret _ _ k (by have := (hbud k hk).2; omega)]
    calc winValue (2*s+3) k / (((2*s+3:ℕ):ℝ)+4)
        ≤ ((((2*s+3:ℕ):ℝ)+3)/((2*s+3:ℕ):ℝ))/(((2*s+3:ℕ):ℝ)+4) :=
          div_le_div_of_nonneg_right
            (winValue_le _ _ (by omega) (by omega) (by have := (hbud k hk).1; omega)
              (hbud k hk).2) hD.le
      _ = _ := by ring
  · have h := le_sup' (fun k => ∑ a : Fin (2*s+3),
        cyclicLaw (2*s+3) a * regret (oddBase (2*s+3)) (cyclicPerm (2*s+3) a)
          (((2*s+3:ℕ):ℝ)+4) k) hlast
    rw [rotated_expected_regret _ _ _ (by omega),winValue_at_last _ (by omega) (by omega)] at h
    convert h using 1 <;> ring

theorem odd_allPerm_witness (s : ℕ) (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (hbud : ∀ k∈budgets, 1≤k ∧ k<2*s+3) (hlast : 2*s+3-1∈budgets) :
    ∃ P ∈ FeasibleAt (id : Equiv.Perm (Fin (2*s+3)) → _) 0,
      maxRegret P (gFamily (2*s+3)) id (((2*s+3:ℕ):ℝ)+4) budgets hne
        = (((2*s+3:ℕ):ℝ)+3)/(((2*s+3:ℕ):ℝ)*(((2*s+3:ℕ):ℝ)+4)) := by
  exact actual_allPerm_witness_of_menu (oddBase (2*s+3)) (gFamily (2*s+3))
    (oddToFamily s) (oddToFamily_apply s) (cyclicLaw (2*s+3)) (cyclicPerm (2*s+3))
    _ 0 _ budgets hne (feasible_zero_nonempty (2*s+3))
    (odd_cyclic_max s budgets hne hbud hlast)

/-- The omitted-item marginal follows from the upper side of the SAME band definition. -/
theorem last_marginal_uniform {m : ℕ} (hm : 0<m)
    (P : Equiv.Perm (Fin m) → ℝ) (hP : P ∈ FeasibleAt id 0) (i : Fin m) :
    (∑ σ, P σ * (if i=σ ⟨m-1,by omega⟩ then (1:ℝ) else 0)) = 1/(m:ℝ) := by
  classical
  have h := hP.2.2 (m-1) (by omega) i
  simp only [zero_div,abs_le_zero,sub_eq_zero] at h
  simp_rw [last_eq_one_sub_inPrefix hm]
  rw [show (∑ σ, P σ*(1-inPrefixInd σ (m-1) i))
      = (∑ σ,P σ) - ∑ σ,P σ*inPrefixInd σ (m-1) i by
        rw [←sum_sub_distrib]; apply sum_congr rfl; intro σ _; ring]
  rw [hP.2.1,h]
  have hmR : (m:ℝ)≠0 := by positivity
  rw [Nat.cast_sub (by omega : 1≤m)]
  push_cast
  field_simp
  ring

/-- Every uniform-band law has the same expected last-budget loss. -/
theorem expected_last_uniform {m : ℕ} (hm : 0<m) (hp : m%2=1)
    (g : Ranking m) (htotal : ∑ i,g i = -1) (D : ℝ)
    (P : Equiv.Perm (Fin m) → ℝ) (hP : P ∈ FeasibleAt id 0) :
    (∑ σ,P σ*regret g σ D (m-1)) = (∑ i,|-1-g i|)/((m:ℝ)*D) := by
  classical
  have hreg : ∀ σ : Equiv.Perm (Fin m),
      regret g σ D (m-1)=|-1-g (σ ⟨m-1,by omega⟩)|/D := by
    intro σ
    unfold regret excess
    rw [prefixSum_pred hm]
    have hs : ∑ i,rankOf g σ i=∑ i,g i := Equiv.sum_comp σ g
    rw [hs,htotal,show (m-1)%2=0 by omega]
    simp [rankOf]
  simp_rw [hreg]
  have hexp : (∑ σ,P σ*|-1-g (σ ⟨m-1,by omega⟩)|)
      = ∑ i,(∑ σ,P σ*(if i=σ ⟨m-1,by omega⟩ then (1:ℝ) else 0))*|-1-g i| := by
    rw [sum_comm]
    apply sum_congr rfl
    intro σ _
    simp only [sum_mul, mul_assoc]
    simp
  rw [show (∑ σ,P σ*(|-1-g (σ ⟨m-1,by omega⟩)|/D))
      = (∑ σ,P σ*|-1-g (σ ⟨m-1,by omega⟩)|)/D by simp [sum_div,mul_div_assoc]]
  rw [hexp]
  simp_rw [last_marginal_uniform hm P hP]
  rw [← mul_sum]
  ring

/-- Reuse the proved last window sum to evaluate the omitted-item sum, without a census. -/
theorem odd_omitted_sum (s : ℕ) :
    (∑ i : Fin (2*s+3),|-1-gFamily (2*s+3) i|) = ((2*s+3:ℕ):ℝ)+3 := by
  classical
  let m := 2*s+3
  have htotal : ∑ i : Fin m, oddBase m i = -1 := by
    simpa [prefixSum] using oddBase_total m (by dsimp [m]; omega) (by dsimp [m]; omega)
  rw [← Equiv.sum_comp (oddToFamily s) (fun i => |-1-gFamily (2*s+3) i|)]
  simp_rw [oddToFamily_apply]
  rw [← htotal, ← sum_rot_abs_prefix (by dsimp [m]; omega) (oddBase m)]
  change (∑ a : Fin m, |prefixSum (rankOf (oddBase m) (cyclicPerm m a)) (m-1)|) = _
  simp_rw [rotated_prefix_eq_win m _ (m-1) (by omega)]
  rw [Fin.sum_univ_eq_sum_range,win_abs_sum_even m (m-1)
    (by dsimp [m]; omega) (by dsimp [m]; omega) (by dsimp [m]; omega)
    (by dsimp [m]; omega) (by dsimp [m]; omega)]
  rw [Nat.cast_sub (by dsimp [m]; omega : 1≤m)]
  push_cast
  dsimp [m]
  ring

theorem odd_allPerm_lower (s : ℕ) (P : Equiv.Perm (Fin (2*s+3)) → ℝ)
    (hP : P∈FeasibleAt id 0) (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (hlast : 2*s+3-1∈budgets) :
    (((2*s+3:ℕ):ℝ)+3)/(((2*s+3:ℕ):ℝ)*(((2*s+3:ℕ):ℝ)+4))
      ≤ maxRegret P (gFamily (2*s+3)) id (((2*s+3:ℕ):ℝ)+4) budgets hne := by
  have ht : ∑ i,gFamily (2*s+3) i = -1 :=
    (gFamily_isOddFamily (2*s+1) (by omega) (by omega)).total
  have heq := expected_last_uniform (by omega : 0<2*s+3) (by omega : (2*s+3)%2=1)
    (gFamily (2*s+3)) ht (((2*s+3:ℕ):ℝ)+4) P hP
  rw [odd_omitted_sum s] at heq
  rw [← heq]
  exact le_sup' _ hlast

theorem odd_allPerm_value (s : ℕ) (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (hbud : ∀ k∈budgets,1≤k ∧ k<2*s+3) (hlast : 2*s+3-1∈budgets) :
    Vm (gFamily (2*s+3)) id (((2*s+3:ℕ):ℝ)+4) 0 budgets hne
      = (((2*s+3:ℕ):ℝ)+3)/(((2*s+3:ℕ):ℝ)*(((2*s+3:ℕ):ℝ)+4)) := by
  obtain ⟨P,hP,hval⟩ := odd_allPerm_witness s budgets hne hbud hlast
  apply le_antisymm
  · have hb := Vm_bddBelow (gFamily (2*s+3)) id (((2*s+3:ℕ):ℝ)+4) 0
      (by positivity) budgets hne (fun k hk => by have := (hbud k hk).2; omega)
      (fun σ i => gFamily_weights (2*s+3) (σ i))
    exact hval ▸ csInf_le hb ⟨P,hP,rfl⟩
  · apply le_csInf (Set.Nonempty.image _ ⟨P,hP⟩)
    rintro _ ⟨Q,hQ,rfl⟩
    exact odd_allPerm_lower s Q hQ budgets hne hlast

#print axioms rotated_prefix_eq_win
#print axioms odd_allPerm_witness
#print axioms expected_last_uniform
#print axioms odd_omitted_sum
#print axioms odd_allPerm_lower
#print axioms odd_allPerm_value
end CIGAMF.P13.PaperCOddWitnessJoin
