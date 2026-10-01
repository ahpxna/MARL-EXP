import «LeanD6SameResponseMarginGameV1»

/-! Finite actual-world matching certificates. k=q+1. The primal randomizes
between T and T-complement. The dual mixes the full hidden intersection with
q+1 singleton-intersection worlds. Both certificates act on actual loss. -/
namespace CIGAMF.P13.D6SameResponseMarginCertificate
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6SameResponseMarginLoss
open CIGAMF.P13.D6SameResponseMarginGame
noncomputable section

def singletonWorld {n : ℕ} (T : Finset (I n)) (j i : I n) := insert i (others T j)

lemma singleton_inter {n : ℕ} (T : Finset (I n)) (j i : I n) (hi : i ∈ T) :
    singletonWorld T j i ∩ T={i} := by
  classical
  ext x
  simp only [singletonWorld,mem_inter,mem_insert,mem_singleton,others,mem_erase,mem_sdiff,mem_univ,true_and]
  constructor
  · intro h
    rcases h.1 with he | hh
    · exact he
    · exact False.elim (hh.2 h.2)
  · intro he
    subst x
    exact ⟨Or.inl rfl,hi⟩

lemma singleton_valid (q : ℕ) (hq : 2 ≤ q) (j : I (2*q+1))
    (T : Finset (I (2*q+1))) (hT : T ∈ worlds q j) (i : I (2*q+1)) (hi : i ∈ T) :
    singletonWorld T j i ∈ worlds q j := by
  classical
  have hp := world_parameters q j hq hT
  have hj : i ≠ j := by intro he;subst i;exact hp.1 hi
  have hnot : i ∉ others T j := by simp [others,hi]
  have hb : (others T j).card=q := by
    change (Tᶜ.erase j).card=q
    rw [card_erase_of_mem (by simp [hp.1]),hp.2.2.1,hp.2.1]
    omega
  apply mem_powersetCard.mpr
  constructor
  · intro x hx
    rcases mem_insert.mp hx with he | hm
    · subst x;simp [positiveGround,hj]
    · exact mem_erase.mpr ⟨(mem_erase.mp hm).1,mem_univ _⟩
  · change (insert i (others T j)).card=q+1
    rw [card_insert_of_notMem hnot,hb]

lemma singleton_average (q : ℕ) (hq : 2 ≤ q) (j : I (2*q+1))
    (T S : Finset (I (2*q+1))) (hT : T ∈ worlds q j) (rho : ℝ) (hr : 1 ≤ rho) :
    (∑ i ∈ T,(loss (singletonWorld T j i) T S j rho-
      loss (singletonWorld T j i) T (singletonWorld T j i)ᶜ j rho))/((q:ℝ)+1)=
      (rho*((T \ S).card:ℝ)-2*((T \ S).card:ℝ)/((q:ℝ)+1)+(2-rho))/2 := by
  classical
  have ht := world_parameters q j hq hT
  let D := T \ S
  have hDdef : D=T \ S := rfl
  have hD : D ⊆ T := sdiff_subset
  have hsum : (∑ i ∈ T,((singletonWorld T j i ∩ D).card:ℝ))=(D.card:ℝ) := by
    have he (i : I (2*q+1)) (hi : i ∈ T) :
        singletonWorld T j i ∩ D=if i ∈ D then {i} else ∅ := by
      have h := singleton_inter T j i hi
      have hid : singletonWorld T j i ∩ D=(singletonWorld T j i ∩ T) ∩ D := by
        ext x;simp only [mem_inter];exact ⟨fun hx => ⟨⟨hx.1,hD hx.2⟩,hx.2⟩,fun hx => ⟨hx.1.1,hx.2⟩⟩
      rw [hid,h]
      by_cases hh : i ∈ D <;> simp [hh]
    have heq : (∑ i ∈ T,((singletonWorld T j i ∩ D).card:ℝ))=
        ∑ i ∈ T,if i ∈ D then (1:ℝ) else 0 := by
      apply sum_congr rfl
      intro i hi
      rw [he i hi]
      split <;> simp
    rw [heq,sum_ite_mem,inter_eq_right.mpr hD]
    simp
  have hpoint (i : I (2*q+1)) (hi : i ∈ T) :
      loss (singletonWorld T j i) T S j rho-loss (singletonWorld T j i) T (singletonWorld T j i)ᶜ j rho=
        (rho*(D.card:ℝ)-2*((singletonWorld T j i ∩ D).card:ℝ)+(2-rho))/2 := by
    have hp := world_parameters q j hq (singleton_valid q hq j T hT i hi)
    rw [actual_regret_formula _ T S j hp.1 ht.1 rho hr hp.2.2.2,singleton_inter T j i hi]
    simp only [card_singleton,Nat.cast_one,mul_one,hDdef]
  have heq := sum_congr rfl hpoint
  have hsplit : ∀ i ∈ T,
      (rho*(D.card:ℝ)-2*((singletonWorld T j i ∩ D).card:ℝ)+(2-rho))/2=
        (rho*(D.card:ℝ)+(2-rho))/2-((singletonWorld T j i ∩ D).card:ℝ) := by
    intro i _;ring
  have hval : (∑ i ∈ T,(rho*(D.card:ℝ)-2*((singletonWorld T j i ∩ D).card:ℝ)+(2-rho))/2)=
      ((q:ℝ)+1)*((rho*(D.card:ℝ)+(2-rho))/2)-(D.card:ℝ) := by
    rw [sum_congr rfl hsplit,sum_sub_distrib,sum_const,nsmul_eq_mul,hsum,ht.2.1]
    push_cast
    ring
  rw [heq,hval]
  change _=(rho*(D.card:ℝ)-2*(D.card:ℝ)/((q:ℝ)+1)+(2-rho))/2
  have hk : (q:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

/-- A normalized nonnegative prior on k+1 actual same-response worlds makes
every decision have exactly the claimed regret. -/
theorem actual_dual_equalizer (q : ℕ) (hq : 2 ≤ q) (j : I (2*q+1))
    (T S : Finset (I (2*q+1))) (hT : T ∈ worlds q j) (rho : ℝ) (hr : 1 ≤ rho) :
    ((((q:ℝ)+1)*rho-2)/(2*q))*(loss T T S j rho-loss T T Tᶜ j rho)+
      (1-(((q:ℝ)+1)*rho-2)/(2*q))*
        ((∑ i ∈ T,(loss (singletonWorld T j i) T S j rho-
          loss (singletonWorld T j i) T (singletonWorld T j i)ᶜ j rho))/((q:ℝ)+1))=
      ((q:ℝ)+1)*rho*(2-rho)/4 := by
  have hp := world_parameters q j hq hT
  rw [singleton_average q hq j T S hT rho hr,
    actual_regret_formula T T S j hp.1 hp.1 rho hr hp.2.2.2]
  have he : T ∩ (T \ S)=T \ S := inter_eq_right.mpr sdiff_subset
  rw [inter_self,he,hp.2.1]
  push_cast
  have ha := adversary_equalizer ((q:ℝ)+1) rho ((T \ S).card:ℝ) (by exact_mod_cast (show 2 ≤ q+1 by omega))
  convert ha using 1 <;> ring

/-- The same prior lower certificate holds against every finite randomized
rule; sum one is its only assumption. -/
theorem randomized_dual_equalizer (q : ℕ) (hq : 2 ≤ q) (j : I (2*q+1))
    (T : Finset (I (2*q+1))) (hT : T ∈ worlds q j) (rho : ℝ) (hr : 1 ≤ rho)
    (S : Finset (Finset (I (2*q+1)))) (p : Finset (I (2*q+1)) → ℝ) (hn : ∑ U ∈ S,p U=1) :
    (∑ U ∈ S,p U*(((((q:ℝ)+1)*rho-2)/(2*q))*(loss T T U j rho-loss T T Tᶜ j rho)+
      (1-(((q:ℝ)+1)*rho-2)/(2*q))*
        ((∑ i ∈ T,(loss (singletonWorld T j i) T U j rho-
          loss (singletonWorld T j i) T (singletonWorld T j i)ᶜ j rho))/((q:ℝ)+1))))=
      ((q:ℝ)+1)*rho*(2-rho)/4 := by
  simp_rw [actual_dual_equalizer q hq j T _ hT rho hr]
  rw [← sum_mul,hn,one_mul]

#print axioms singleton_valid
#print axioms singleton_average
#print axioms actual_dual_equalizer
#print axioms randomized_dual_equalizer
end
end CIGAMF.P13.D6SameResponseMarginCertificate
