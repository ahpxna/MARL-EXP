import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset

/-! Exact first and second moments of uniform fixed-size subsets, derived by
counting actual subsets. No stochastic moment identity is supplied as a premise. -/
namespace CIGAMF.P13.UniformSubsetMoments
open scoped BigOperators
open Finset
noncomputable section
variable {α : Type*} [DecidableEq α]

def hit (G : Finset α) (i : α) : ℝ := if i ∈ G then 1 else 0

def avg (U : Finset α) (r : ℕ) (f : Finset α → ℝ) : ℝ :=
  (∑ G ∈ U.powersetCard r,f G)/(U.powersetCard r).card

lemma count_hit (U : Finset α) (r : ℕ) (hr : 1 ≤ r) (i : α) (hi : i ∈ U) :
    (∑ G ∈ U.powersetCard r,hit G i)=((U.card-1).choose (r-1):ℝ) := by
  have h := card_filter_powersetCard_subset {i} U r (singleton_subset_iff.mpr hi) (by simpa using hr)
  have he : (∑ G ∈ U.powersetCard r,hit G i)=
      (((U.powersetCard r).filter (fun G => {i} ⊆ G)).card:ℝ) := by
    simp [hit,singleton_subset_iff]
  rw [he,h,card_singleton]

lemma count_hit_pair (U : Finset α) (r : ℕ) (hr : 2 ≤ r) (i j : α)
    (hi : i ∈ U) (hj : j ∈ U) :
    (∑ G ∈ U.powersetCard r,hit G i*hit G j)=
      if i=j then ((U.card-1).choose (r-1):ℝ) else ((U.card-2).choose (r-2):ℝ) := by
  by_cases hij : i=j
  · subst j
    simp only [ite_true]
    have he : ∀ G : Finset α,hit G i*hit G i=hit G i := by intro G; unfold hit; split <;> norm_num
    simp_rw [he]
    exact count_hit U r (by omega) i hi
  · rw [if_neg hij]
    have hcard : ({i,j}:Finset α).card=2 := by simp [hij]
    have h := card_filter_powersetCard_subset {i,j} U r
      (insert_subset_iff.mpr ⟨hi,singleton_subset_iff.mpr hj⟩) (by rw [hcard]; exact hr)
    have he : ∀ G : Finset α,hit G i*hit G j=if {i,j} ⊆ G then 1 else 0 := by
      intro G
      by_cases h1 : i ∈ G <;> by_cases h2 : j ∈ G <;> simp [hit,h1,h2,insert_subset_iff,singleton_subset_iff]
    simp_rw [he]
    have hc : (∑ G ∈ U.powersetCard r,if {i,j} ⊆ G then (1:ℝ) else 0)=
        (((U.powersetCard r).filter (fun G => {i,j} ⊆ G)).card:ℝ) := by simp
    rw [hc,h,hcard]

lemma sum_weighted (U : Finset α) (r : ℕ) (hr : 1 ≤ r) (v : α → ℝ) :
    (∑ G ∈ U.powersetCard r,∑ i ∈ G,v i)=
      ((U.card-1).choose (r-1):ℝ)*(∑ i ∈ U,v i) := by
  have he : ∀ G ∈ U.powersetCard r,(∑ i ∈ G,v i)=∑ i ∈ U,hit G i*v i := by
    intro G hG
    rw [← sum_subset (mem_powersetCard.mp hG).1 (by intro i _ hi; simp [hit,hi])]
    apply sum_congr rfl
    intro i hi
    simp [hit,hi]
  rw [sum_congr rfl he,sum_comm,mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [← sum_mul,count_hit U r hr i hi]

lemma sum_weighted_sq (U : Finset α) (r : ℕ) (hr : 2 ≤ r) (v : α → ℝ) :
    (∑ G ∈ U.powersetCard r,(∑ i ∈ G,v i)^2)=
      (((U.card-1).choose (r-1):ℝ)-((U.card-2).choose (r-2):ℝ))*(∑ i ∈ U,(v i)^2)+
      ((U.card-2).choose (r-2):ℝ)*(∑ i ∈ U,v i)^2 := by
  have he : ∀ G ∈ U.powersetCard r,(∑ i ∈ G,v i)=∑ i ∈ U,hit G i*v i := by
    intro G hG
    rw [← sum_subset (mem_powersetCard.mp hG).1 (by intro i _ hi; simp [hit,hi])]
    apply sum_congr rfl; intro i hi; simp [hit,hi]
  have hexp : ∀ G ∈ U.powersetCard r,(∑ i ∈ G,v i)^2=
      ∑ i ∈ U,∑ j ∈ U,(hit G i*hit G j)*(v i*v j) := by
    intro G hG
    rw [he G hG,pow_two,sum_mul_sum]
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj
    ring
  rw [sum_congr rfl hexp,sum_comm]
  simp_rw [sum_comm (s := U.powersetCard r),← sum_mul]
  have hp : ∀ i ∈ U,∀ j ∈ U,(∑ G ∈ U.powersetCard r,hit G i*hit G j)=
      ((U.card-2).choose (r-2):ℝ)+
        if i=j then ((U.card-1).choose (r-1):ℝ)-((U.card-2).choose (r-2):ℝ) else 0 := by
    intro i hi j hj
    rw [count_hit_pair U r hr i j hi hj]
    split <;> ring
  simp_rw [sum_congr rfl (fun i hi => sum_congr rfl (fun j hj => congrArg
    (fun x : ℝ => x*(v i*v j)) (hp i hi j hj)))]
  simp only [add_mul,sum_add_distrib,ite_mul,zero_mul]
  simp only [sum_ite_eq,Finset.sum_ite_eq',sum_const_zero]
  simp only [← mul_sum,← sum_mul]
  have hdiag : (∑ i ∈ U,if i ∈ U then
      (((U.card-1).choose (r-1):ℝ)-((U.card-2).choose (r-2):ℝ))*(v i*v i) else 0)=
      (((U.card-1).choose (r-1):ℝ)-((U.card-2).choose (r-2):ℝ))*(∑ i ∈ U,(v i)^2) := by
    rw [mul_sum]; apply sum_congr rfl; intro i hi; simp [hi,pow_two]
  rw [hdiag]
  ring

lemma choose_ratios (n r : ℕ) (hr : 2 ≤ r) (hrn : r ≤ n) :
    ((n-1).choose (r-1):ℝ)/(n.choose r)=r/(n:ℝ) ∧
    ((n-2).choose (r-2):ℝ)/(n.choose r)=
      (r:ℝ)*(r-1)/((n:ℝ)*(n-1)) := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hn1 : 0 < (n:ℝ)-1 := by linarith
  have hc : 0 < (n.choose r:ℝ) := by exact_mod_cast Nat.choose_pos hrn
  have h1 := Nat.add_one_mul_choose_eq (n-1) (r-1)
  have h2 := Nat.add_one_mul_choose_eq (n-2) (r-2)
  have hn' : n-1+1=n := by omega
  have hr' : r-1+1=r := by omega
  have hn'' : n-2+1=n-1 := by omega
  have hr'' : r-2+1=r-1 := by omega
  rw [hn',hr'] at h1
  rw [hn'',hr''] at h2
  have h1r : (n:ℝ)*((n-1).choose (r-1):ℝ)=(n.choose r:ℝ)*r := by exact_mod_cast h1
  have h2r : ((n:ℝ)-1)*((n-2).choose (r-2):ℝ)=((n-1).choose (r-1):ℝ)*(r-1) := by
    have hh : ((n-1:ℕ):ℝ)*((n-2).choose (r-2):ℝ)=
        ((n-1).choose (r-1):ℝ)*(r-1:ℕ) := by exact_mod_cast h2
    simpa only [Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_sub (show 1 ≤ r by omega),Nat.cast_one] using hh
  constructor
  · apply (div_eq_div_iff (ne_of_gt hc) (ne_of_gt hn)).mpr
    nlinarith only [h1r]
  · apply (div_eq_div_iff (ne_of_gt hc) (ne_of_gt (mul_pos hn hn1))).mpr
    nlinarith only [congrArg (fun x : ℝ => (n:ℝ)*x) h2r,
      congrArg (fun x : ℝ => x*((r:ℝ)-1)) h1r]

theorem average_weighted (U : Finset α) (r : ℕ) (hr : 2 ≤ r) (hrU : r ≤ U.card) (v : α → ℝ) :
    avg U r (fun G => ∑ i ∈ G,v i)=(r:ℝ)/U.card*(∑ i ∈ U,v i) := by
  unfold avg
  rw [sum_weighted U r (by omega) v,card_powersetCard]
  rw [mul_div_right_comm, (choose_ratios U.card r hr hrU).1]

theorem average_weighted_sq (U : Finset α) (r : ℕ) (hr : 2 ≤ r) (hrU : r ≤ U.card) (v : α → ℝ) :
    avg U r (fun G => (∑ i ∈ G,v i)^2)=
      ((r:ℝ)/U.card-(r:ℝ)*(r-1)/((U.card:ℝ)*(U.card-1)))*(∑ i ∈ U,(v i)^2)+
      ((r:ℝ)*(r-1)/((U.card:ℝ)*(U.card-1)))*(∑ i ∈ U,v i)^2 := by
  unfold avg
  rw [sum_weighted_sq U r hr v,card_powersetCard,add_div]
  simp only [sub_mul,sub_div,mul_div_right_comm]
  rw [(choose_ratios U.card r hr hrU).1,(choose_ratios U.card r hr hrU).2]
  ring

#print axioms count_hit
#print axioms count_hit_pair
#print axioms sum_weighted_sq
#print axioms average_weighted
#print axioms average_weighted_sq
end
end CIGAMF.P13.UniformSubsetMoments
