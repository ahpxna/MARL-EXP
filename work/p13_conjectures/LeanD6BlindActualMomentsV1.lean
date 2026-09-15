import «LeanUniformSubsetMomentsV1»
import «LeanD6PhaseThreePrimalV1»
import «LeanD6BlindSaddleCertificateV1»

/-! Uniform actual scalar and size-q off-query information, for every hidden
world and every same-size alternative. This file derives the coefficients
from finite query sums, not from a supplied orbit or Gaussian-moment formula. -/
namespace CIGAMF.P13.D6BlindActualMoments
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationFiniteBridge
open CIGAMF.P13.D6AllocationPrimalBridge CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6PhaseThreePrimal
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

lemma ground_partition (A : Finset (I n)) (j : I n) (hj : j ∉ A) :
    A ∪ others A j=univ.erase j := by
  ext i
  by_cases hi : i=j
  · subst i; simp [others,hj]
  · simp [others,hi]; tauto

lemma others_card_eq (A A' : Finset (I n)) (j : I n)
    (hj : j ∉ A) (hj' : j ∉ A') (hc : A'.card=A.card) :
    (others A' j).card=(others A j).card := by
  have h1 : (others A j).card=n-A.card := by
    unfold others
    rw [card_erase_of_mem (by simp [hj]),card_sdiff_of_subset (subset_univ A)]
    simp [I] <;> omega
  have h2 : (others A' j).card=n-A'.card := by
    unfold others
    rw [card_erase_of_mem (by simp [hj']),card_sdiff_of_subset (subset_univ A')]
    simp [I] <;> omega
  rw [h1,h2,hc]

lemma sum_hit_ground (B : Finset (I n)) (j : I n) (hj : j ∉ B) :
    (∑ i ∈ univ.erase j,hit B i)=(B.card:ℝ) := by
  rw [sum_hit,inter_eq_left.mpr]
  intro i hi
  exact mem_erase.mpr ⟨by intro he; subst i; exact hj hi,mem_univ i⟩

lemma sum_hit_cross (B C : Finset (I n)) (j : I n) (hj : j ∉ B) :
    (∑ i ∈ univ.erase j,hit B i*hit C i)=((B ∩ C).card:ℝ) := by
  have he : ∀ i,hit B i*hit C i=hit (B ∩ C) i := by
    intro i
    by_cases hb : i ∈ B <;> by_cases hc : i ∈ C <;> simp [hit,hb,hc]
  simp_rw [he]
  exact sum_hit_ground _ j (by simp [hj])

lemma population_moments (B C : Finset (I n)) (j : I n) (hjB : j ∉ B) (hjC : j ∉ C)
    (b c : ℝ) :
    (∑ i ∈ univ.erase j,(b*hit B i+c*hit C i))=b*B.card+c*C.card ∧
    (∑ i ∈ univ.erase j,(b*hit B i+c*hit C i)^2)=
      b^2*B.card+2*b*c*(B ∩ C).card+c^2*C.card := by
  constructor
  · simp only [sum_add_distrib,← mul_sum,sum_hit_ground B j hjB,sum_hit_ground C j hjC]
  · have he : ∀ i,(b*hit B i+c*hit C i)^2=
        b^2*hit B i+2*b*c*(hit B i*hit C i)+c^2*hit C i := by
      intro i
      by_cases hb : i ∈ B <;> by_cases hc : i ∈ C <;> simp [hit,hb,hc] <;> ring
    simp_rw [he]
    simp only [sum_add_distrib,← mul_sum,sum_hit_ground B j hjB,sum_hit_ground C j hjC,
      sum_hit_cross B C j hjB]

/-- Mean difference as a sum of actual coordinate-membership coefficients. -/
lemma actual_off_difference (A A' G : Finset (I n)) (j : I n) (mu z : ℝ)
    (hj : j ∉ A) (hj' : j ∉ A') (hjG : j ∉ G) (hG : 2 ≤ G.card) :
    world A j mu (query G j false)-world A' j (mu+z) (query G j false)=
      ∑ i ∈ G,((1-mu)*hit (others A j) i-(1-mu-z)*hit (others A' j) i) := by
  rw [actual_query_mean A G j false hj hjG (by intro _; exact hG),
    actual_query_mean A' G j false hj' hjG (by intro _; exact hG)]
  simp only [Bool.false_eq_true,↓reduceIte,bit_false,sub_zero,sum_sub_distrib,← mul_sum,sum_hit,
    inter_comm (others A j) G,inter_comm (others A' j) G]
  ring

/-- Population moments have no dependence on the names of the hidden labels. -/
lemma actual_population_moments (A A' : Finset (I n)) (j : I n) (q mu z : ℝ)
    (hj : j ∉ A) (hj' : j ∉ A') (hc : A'.card=A.card)
    (hB : ((others A j).card:ℝ)=q) :
    (∑ i ∈ univ.erase j,((1-mu)*hit (others A j) i-(1-mu-z)*hit (others A' j) i))=q*z ∧
    (∑ i ∈ univ.erase j,((1-mu)*hit (others A j) i-(1-mu-z)*hit (others A' j) i)^2)=
      q*z^2+2*(A \ A').card*((1-mu)^2-(1-mu)*z) := by
  have hm := population_moments (others A j) (others A' j) j (by simp [others])
    (by simp [others]) (1-mu) (-(1-mu-z))
  rw [others_card_eq A A' j hj hj' hc,hB,B_alternative_count A A' j hj' hc,hB] at hm
  simp only [neg_mul,← sub_eq_add_neg] at hm
  constructor
  · rw [hm.1]; ring
  · rw [hm.2]; ring

/-- The uniform size-q off design is legal and does not use A. -/
theorem qoff_legal (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1)) :
    ∀ G ∈ (univ.erase j).powersetCard q,Legal j q (.inr (G,false)) := by
  intro G hG
  have h := mem_powersetCard.mp hG
  refine ⟨?_,?_,?_⟩
  · intro hj; exact (mem_erase.mp (h.1 hj)).1 rfl
  · exact_mod_cast h.2.le
  · intro _; omega

/-- Exact average KL over all actual size-q off queries, for every alternative
and every real nuisance shift. -/
theorem actual_qoff_average (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (A A' : Finset (I (2*q+1))) (hj : j ∉ A) (hj' : j ∉ A')
    (hc : A'.card=A.card) (hB : (others A j).card=q) (mu z : ℝ) :
    UniformSubsetMoments.avg (univ.erase j) q (fun G => queryKL A A' G j false mu (mu+z))=
      (q:ℝ)*(q^2+1)/(2*(2*q+1))*z^2/2+
        (A \ A').card*(q+1)/(2*(2*q+1))*((1-mu)^2-(1-mu)*z) := by
  let v := fun i => (1-mu)*hit (others A j) i-(1-mu-z)*hit (others A' j) i
  have hU : (univ.erase j).card=2*q+1 := by simp [I]
  have hh := UniformSubsetMoments.average_weighted_sq (univ.erase j) q (by omega)
    (by rw [hU]; omega) v
  have hm := actual_population_moments A A' j q mu z hj hj' hc (by exact_mod_cast hB)
  have he : UniformSubsetMoments.avg (univ.erase j) q (fun G => queryKL A A' G j false mu (mu+z))=
      UniformSubsetMoments.avg (univ.erase j) q (fun G => (∑ i ∈ G,v i)^2)/2 := by
    have hs : (∑ G ∈ (univ.erase j).powersetCard q,queryKL A A' G j false mu (mu+z))=
        (∑ G ∈ (univ.erase j).powersetCard q,(∑ i ∈ G,v i)^2)/2 := by
      rw [sum_div]
      apply sum_congr rfl
      intro G hG
      have hl := qoff_legal q hq j G hG
      unfold queryKL
      rw [actual_off_difference A A' G j mu z hj hj' hl.1 (hl.2.2 rfl)]
    unfold UniformSubsetMoments.avg
    rw [hs]
    ring
  rw [he,hh]
  change _ = _
  dsimp [v]
  rw [hm.1,hm.2,hU]
  push_cast
  have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hn0 : 2*(q:ℝ)+1 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Uniform non-j scalar KL for arbitrary exchange distance. -/
theorem actual_scalar_average (A A' : Finset (I n)) (j : I n) (q mu z : ℝ)
    (hj : j ∉ A) (hj' : j ∉ A') (hc : A'.card=A.card)
    (hB : ((others A j).card:ℝ)=q) :
    (∑ i ∈ univ.erase j,scalarKL A A' j i mu (mu+z))/n=
      (q*z^2/2+(A \ A').card*mu*z+(A \ A').card*mu^2)/n := by
  have hp := population_moments (others A j) (others A' j) j (by simp [others])
    (by simp [others]) (-mu) (mu+z)
  rw [others_card_eq A A' j hj hj' hc,hB,B_alternative_count A A' j hj' hc,hB] at hp
  have he : (∑ i ∈ univ.erase j,scalarKL A A' j i mu (mu+z))=
      (∑ i ∈ univ.erase j,((-mu)*hit (others A j) i+(mu+z)*hit (others A' j) i)^2)/2 := by
    rw [sum_div]
    apply sum_congr rfl; intro i hi
    have hij := (mem_erase.mp hi).1
    unfold scalarKL
    rw [world_response A j hj,world_response A' j hj']
    by_cases hia : i ∈ A <;> by_cases hib : i ∈ A' <;>
      simp [CIGAMF.P13.D6Threshold.slope,hia,hib,hij,hit,others,bit_true] <;> ring
  rw [he,hp.2]
  ring

#print axioms population_moments
#print axioms actual_population_moments
#print axioms qoff_legal
#print axioms actual_qoff_average
#print axioms actual_scalar_average
end
end CIGAMF.P13.D6BlindActualMoments
