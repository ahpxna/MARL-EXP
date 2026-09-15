import «LeanD6GaussianQueryDominanceV1»
import «LeanGaussianThresholdDecisionV1»

/-! Three fixed legal queries remove the hidden label from phase observations. -/
namespace CIGAMF.P13.D6BlindPhaseBlocks
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.AdaptiveTranscriptKernel
open CIGAMF.P13.GaussianSampleProduct CIGAMF.P13.GaussianProductOverlap
open CIGAMF.P13.D6GaussianOverlap
noncomputable section
variable {n : ℕ}

structure ThreePartition (j : I n) (q : ℕ) where
  first : Finset (I n)
  second : Finset (I n)
  third : Finset (I n)
  disjoint12 : Disjoint first second
  disjoint13 : Disjoint first third
  disjoint23 : Disjoint second third
  cover : (first ∪ second) ∪ third = univ.erase j
  card1 : first.card = q
  card2 : second.card = q-1
  card3 : third.card = 2

/-- This partition exists without receiving A or mu. -/
theorem partition_exists (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1)) :
    Nonempty (ThreePartition j q) := by
  classical
  let U : Finset (I (2*q+1)) := univ.erase j
  have hcU : U.card=2*q+1 := by simp [U,I]
  obtain ⟨G1,h1,c1⟩ := exists_subset_card_eq (s := U) (n := q) (by omega)
  have hcR : (U \ G1).card=q+1 := by rw [card_sdiff_of_subset h1,hcU,c1]; omega
  obtain ⟨G2,h2,c2⟩ := exists_subset_card_eq (s := U \ G1) (n := q-1) (by omega)
  let G3 := (U \ G1) \ G2
  have c3 : G3.card=2 := by rw [card_sdiff_of_subset h2,hcR,c2]; omega
  have h12 : Disjoint G1 G2 := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (mem_sdiff.mp (h2 hy)).2 hx
  have h13 : Disjoint G1 G3 := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (mem_sdiff.mp (mem_sdiff.mp hy).1).2 hx
  have h23 : Disjoint G2 G3 := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (mem_sdiff.mp hy).2 hx
  have hcov : (G1 ∪ G2) ∪ G3=U := by
    ext x
    simp only [mem_union,mem_sdiff,G3]
    constructor
    · rintro ((h | h) | h)
      · exact h1 h
      · exact (mem_sdiff.mp (h2 h)).1
      · exact h.1.1
    · intro hx
      by_cases ha : x ∈ G1
      · exact Or.inl (Or.inl ha)
      · by_cases hb : x ∈ G2
        · exact Or.inl (Or.inr hb)
        · exact Or.inr ⟨⟨hx,ha⟩,hb⟩
  exact ⟨⟨G1,G2,G3,h12,h13,h23,hcov,c1,c2,c3⟩⟩

variable {q : ℕ} {j : I n}

theorem partition_legal (p : ThreePartition j q) (hq : 3 ≤ q) :
    Legal j q (.inr (p.first,false)) ∧ Legal j q (.inr (p.second,false)) ∧
      Legal j q (.inr (p.third,false)) := by
  have hn : j ∉ (p.first ∪ p.second) ∪ p.third := by rw [p.cover]; simp
  simp only [mem_union,not_or] at hn
  refine ⟨⟨hn.1.1,?_,?_⟩,⟨hn.1.2,?_,?_⟩,⟨hn.2,?_,?_⟩⟩
  · rw [p.card1]
  · intro _; rw [p.card1]; omega
  · exact_mod_cast (by rw [p.card2]; omega : p.second.card ≤ q)
  · intro _; rw [p.card2]; omega
  · exact_mod_cast (by rw [p.card3]; omega : p.third.card ≤ q)
  · intro _; rw [p.card3]

lemma partition_counts (p : ThreePartition j q) (B : Finset (I n)) (hjB : j ∉ B) :
    (p.first ∩ B).card+(p.second ∩ B).card+(p.third ∩ B).card=B.card := by
  have h12 : Disjoint (p.first ∩ B) (p.second ∩ B) :=
    p.disjoint12.mono inter_subset_left inter_subset_left
  have h13 : Disjoint (p.first ∩ B) (p.third ∩ B) :=
    p.disjoint13.mono inter_subset_left inter_subset_left
  have h23 : Disjoint (p.second ∩ B) (p.third ∩ B) :=
    p.disjoint23.mono inter_subset_left inter_subset_left
  have he : ((p.first ∩ B) ∪ (p.second ∩ B)) ∪ (p.third ∩ B)=B := by
    have hd : ((p.first ∩ B) ∪ (p.second ∩ B)) ∪ (p.third ∩ B)=
        ((p.first ∪ p.second) ∪ p.third) ∩ B := by ext x; simp; tauto
    rw [hd,p.cover]
    ext x
    simp only [mem_inter,mem_erase,mem_univ,true_and,and_true]
    constructor
    · exact fun h => h.2
    · intro hx
      exact ⟨by intro h; subst x; exact hjB hx,hx⟩
  rw [← card_union_of_disjoint h12,← card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h13,h23⟩),he]

/-- Exact identity on the actual D6 world, for every hidden A. -/
theorem actual_block_mean (p : ThreePartition j q) (hq : 3 ≤ q)
    (A : Finset (I n)) (hj : j ∉ A) (hB : (others A j).card=q) (mu : ℝ) :
    actualMean A j mu (.inr (p.first,false))+
      actualMean A j mu (.inr (p.second,false))+
      actualMean A j mu (.inr (p.third,false))=3+q*(1-mu) := by
  have hl := partition_legal p hq
  have hc := partition_counts p (others A j) (by simp [others])
  rw [hB] at hc
  have hcr : ((p.first ∩ others A j).card:ℝ)+(p.second ∩ others A j).card+
      (p.third ∩ others A j).card=q := by exact_mod_cast hc
  rw [actual_mean_affine A j hj q mu _ hl.1,
    actual_mean_affine A j hj q mu _ hl.2.1,actual_mean_affine A j hj q mu _ hl.2.2]
  simp only [meanOffset,meanSlope,Bool.false_eq_true,↓reduceIte,bit_false,sub_zero]
  rw [← hcr]
  ring

abbrev Triple := (ℝ × ℝ) × ℝ

def blockLaw (p : ThreePartition j q) (A : Finset (I n)) (mu : ℝ) : Measure Triple :=
  ((gaussianReal (actualMean A j mu (.inr (p.first,false))) 1).prod
    (gaussianReal (actualMean A j mu (.inr (p.second,false))) 1)).prod
      (gaussianReal (actualMean A j mu (.inr (p.third,false))) 1)

instance blockProbability (p : ThreePartition j q) (A : Finset (I n)) (mu : ℝ) :
    IsProbabilityMeasure (blockLaw p A mu) := by unfold blockLaw; infer_instance

def blockSum (x : Triple) : ℝ := x.1.1+x.1.2+x.2

lemma gaussian_triple_sum (a b c : ℝ) :
    HasLaw blockSum (gaussianReal (a+b+c) 3)
      (((gaussianReal a 1).prod (gaussianReal b 1)).prod (gaussianReal c 1)) := by
  let P := (gaussianReal a 1).prod (gaussianReal b 1)
  have hx : HasLaw (Prod.fst : ℝ × ℝ → ℝ) (gaussianReal a 1) P := by
    refine ⟨by fun_prop,?_⟩; simp [P]
  have hy : HasLaw (Prod.snd : ℝ × ℝ → ℝ) (gaussianReal b 1) P := by
    refine ⟨by fun_prop,?_⟩; simp [P]
  have hxy : HasLaw (fun x : ℝ × ℝ => x.1+x.2) (gaussianReal (a+b) 2) P := by
    refine ⟨by fun_prop,?_⟩
    have hh := gaussianReal_add_gaussianReal_of_indepFun
      (indepFun_prod measurable_id measurable_id) hx hy
    change Measure.map (fun x : ℝ × ℝ => x.1+x.2) P=gaussianReal (a+b) (1+1) at hh
    norm_num at hh
    exact hh
  have hfst : HasLaw (Prod.fst : Triple → ℝ × ℝ) P (P.prod (gaussianReal c 1)) := by
    refine ⟨by fun_prop,?_⟩; simp
  have hz : HasLaw (Prod.snd : Triple → ℝ) (gaussianReal c 1) (P.prod (gaussianReal c 1)) := by
    refine ⟨by fun_prop,?_⟩; simp
  have hi : IndepFun (fun x : Triple => x.1.1+x.1.2) Prod.snd (P.prod (gaussianReal c 1)) :=
    (indepFun_prod measurable_id measurable_id).comp
      (show Measurable (fun x : ℝ × ℝ => x.1+x.2) by fun_prop) measurable_id
  refine ⟨by unfold blockSum; fun_prop,?_⟩
  have hh := gaussianReal_add_gaussianReal_of_indepFun hi (hxy.fun_comp hfst) hz
  change Measure.map blockSum (P.prod (gaussianReal c 1))=gaussianReal (a+b+c) (2+1) at hh
  norm_num at hh
  exact hh

/-- Distribution on three raw independent query observations. -/
theorem actual_block_law (p : ThreePartition j q) (hq : 3 ≤ q)
    (A : Finset (I n)) (hj : j ∉ A) (hB : (others A j).card=q) (mu : ℝ) :
    HasLaw blockSum (gaussianReal (3+q*(1-mu)) 3) (blockLaw p A mu) := by
  have h := gaussian_triple_sum
    (actualMean A j mu (.inr (p.first,false)))
    (actualMean A j mu (.inr (p.second,false)))
    (actualMean A j mu (.inr (p.third,false)))
  rw [actual_block_mean p hq A hj hB mu] at h
  exact h

/-- Centering uses q and the known boundary, never A or the true margin. -/
def blockScore (q : ℕ) (mu0 : ℝ) (x : Triple) : ℝ :=
  (3+q*(1-mu0)-blockSum x)/Real.sqrt 3

theorem actual_score_law (p : ThreePartition j q) (hq : 3 ≤ q)
    (A : Finset (I n)) (hj : j ∉ A) (hB : (others A j).card=q) (mu mu0 : ℝ) :
    HasLaw (blockScore q mu0) (gaussianReal (q*(mu-mu0)/Real.sqrt 3) 1) (blockLaw p A mu) := by
  have h := gaussianReal_div_const
    (gaussianReal_const_sub (actual_block_law p hq A hj hB mu) (3+q*(1-mu0))) (Real.sqrt 3)
  have hv0 : NNReal.mk ((Real.sqrt (3:ℝ))^2) (sq_nonneg _) = (3:NNReal) := by
    apply NNReal.coe_injective
    exact Real.sq_sqrt (by norm_num)
  have he : 3+(q:ℝ)*(1-mu0)-(3+q*(1-mu))=q*(mu-mu0) := by ring
  change HasLaw (fun x : Triple => (3+(q:ℝ)*(1-mu0)-blockSum x)/Real.sqrt 3) _ _
  simpa only [he,hv0,div_self (by norm_num : (3:NNReal) ≠ 0)] using h

#print axioms partition_exists
#print axioms partition_legal
#print axioms actual_block_mean
#print axioms actual_block_law
#print axioms actual_score_law
end
end CIGAMF.P13.D6BlindPhaseBlocks
