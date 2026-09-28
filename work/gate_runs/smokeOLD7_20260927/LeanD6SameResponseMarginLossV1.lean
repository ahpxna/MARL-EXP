import «LeanD6SharpMarginSteeringV1»

/-! World-dependent modular compensation pins the entire corner response to
rho*1_T, while preserving mixed differences. The compression loss is computed
on actual binary worlds, not postulated as a regret table. rho >= 1. -/
namespace CIGAMF.P13.D6SameResponseMarginLoss
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6SharpMarginSteering
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
noncomputable section
variable {n : ℕ}

def compensation (A T : Finset (I n)) (rho : ℝ) (i : I n) : ℝ :=
  (if i ∈ T then rho else 0)-(if i ∈ A then 1 else 0)
def fibreWorld (A T : Finset (I n)) (j : I n) (rho : ℝ) (x : I n → Bool) : ℝ :=
  world A j 1 x+linear (compensation A T rho) x

theorem common_response (A T : Finset (I n)) (j : I n) (hj : j ∉ A)
    (rho : ℝ) (i : I n) (u : Bool) :
    productResponse corner (fibreWorld A T j rho) i u=(if i ∈ T then rho else 0)*bit u := by
  rw [corner_response]
  have hw := world_response A j hj 1 i u
  rw [corner_response] at hw
  have hl := linear_difference (compensation A T rho) zero i u false
  rw [show Function.update (zero : I n → Bool) i false=zero from Function.update_eq_self i zero,
    linear_zero,bit_false] at hl
  simp only [sub_zero] at hl
  dsimp only [fibreWorld]
  rw [hw,hl]
  by_cases hi : i ∈ A <;> by_cases ht : i ∈ T <;> simp [D6Threshold.slope,compensation,hi,ht] <;> ring

theorem mixed_unchanged (A T : Finset (I n)) (j i : I n) (rho : ℝ) (x c : I n → Bool) :
    mixedDifference (fibreWorld A T j rho) i x c=mixedDifference (world A j 1) i x c := by
  have hx := linear_difference (compensation A T rho) x i (x i) (c i)
  have hc := linear_difference (compensation A T rho) c i (x i) (c i)
  rw [Function.update_eq_self] at hx
  rw [Function.update_eq_self] at hc
  unfold mixedDifference fibreWorld
  linarith

lemma actual_residual (A T S : Finset (I n)) (j : I n) (hj : j ∉ A)
    (rho : ℝ) (x : I n → Bool) :
    fibreWorld A T j rho x-∑ i ∈ S,productResponse corner (fibreWorld A T j rho) i (x i)=
      gate A j x+linear (compensation A (T \ S) rho) x := by
  classical
  simp_rw [common_response A T j hj]
  simp only [fibreWorld,world_one_gate,linear,compensation,sub_mul,ite_mul,zero_mul,one_mul,sum_sub_distrib,sum_ite_mem,univ_inter]
  have hh : (∑ i ∈ T,rho*bit (x i))-(∑ i ∈ S ∩ T,rho*bit (x i))=
      ∑ i ∈ T \ S,rho*bit (x i) := by
    have he : T \ (S ∩ T)=T \ S := by ext i;simp only [mem_sdiff,mem_inter];tauto
    have hsum := sum_sdiff (s₁:=S ∩ T) (s₂:=T) (f:=fun i => rho*bit (x i)) inter_subset_right
    rw [he] at hsum
    linarith
  linarith

def lowerCoeff (A D : Finset (I n)) (i : I n) : ℝ := if i ∈ A \ D then -1 else 0
def upperCoeff (A D : Finset (I n)) (rho : ℝ) (i : I n) : ℝ :=
  (if i ∈ D then rho else 0)-(if i ∈ A ∩ D then 1 else 0)

lemma coefficient_bounds (A D : Finset (I n)) (rho : ℝ) (hr : 1 ≤ rho)
    (i : I n) (b : Bool) :
    lowerCoeff A D i ≤ compensation A D rho i*bit b ∧
      compensation A D rho i*bit b ≤ upperCoeff A D rho i := by
  classical
  by_cases ha : i ∈ A <;> by_cases hd : i ∈ D <;> cases b <;>
    simp [lowerCoeff,upperCoeff,compensation,ha,hd] <;> linarith

lemma linear_bounds (A D : Finset (I n)) (rho : ℝ) (hr : 1 ≤ rho) (x : I n → Bool) :
    -((A \ D).card:ℝ) ≤ linear (compensation A D rho) x ∧
    linear (compensation A D rho) x ≤ rho*(D.card:ℝ)-((A ∩ D).card:ℝ) := by
  have hl := sum_le_sum (fun i (_ : i ∈ univ) => (coefficient_bounds A D rho hr i (x i)).1)
  have hu := sum_le_sum (fun i (_ : i ∈ univ) => (coefficient_bounds A D rho hr i (x i)).2)
  simpa only [linear,lowerCoeff,upperCoeff,sum_sub_distrib,sum_ite_mem,univ_inter,
    sum_const,nsmul_eq_mul,mul_neg,mul_one,mul_comm,neg_one_mul] using And.intro hl hu

def lo (A D : Finset (I n)) (j : I n) : I n → Bool := fun i => decide (i=j ∨ i ∈ A \ D)
def hi (A D : Finset (I n)) (j : I n) : I n → Bool := fun i => decide (i≠j ∧ i ∉ A \ D)

lemma lo_linear (A D : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjD : j ∉ D) (rho : ℝ) :
    linear (compensation A D rho) (lo A D j)=-((A \ D).card:ℝ) := by
  classical
  have he (i : I n) : compensation A D rho i*bit (lo A D j i)=lowerCoeff A D i := by
    by_cases hij : i=j
    · subst i;simp [lo,compensation,lowerCoeff,hjA,hjD]
    · by_cases ha : i ∈ A <;> by_cases hd : i ∈ D <;>
        simp [lo,compensation,lowerCoeff,bit,hij,ha,hd]
  simp only [linear,he,lowerCoeff,sum_ite_mem,univ_inter,sum_const,nsmul_eq_mul,mul_neg,mul_one]

lemma hi_linear (A D : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjD : j ∉ D) (rho : ℝ) :
    linear (compensation A D rho) (hi A D j)=rho*(D.card:ℝ)-((A ∩ D).card:ℝ) := by
  classical
  have he (i : I n) : compensation A D rho i*bit (hi A D j i)=upperCoeff A D rho i := by
    by_cases hij : i=j
    · subst i;simp [hi,compensation,upperCoeff,hjA,hjD]
    · by_cases ha : i ∈ A <;> by_cases hd : i ∈ D <;>
        simp [hi,compensation,upperCoeff,bit,hij,ha,hd]
  simp only [linear,he,upperCoeff,sum_sub_distrib,sum_ite_mem,univ_inter,
    sum_const,nsmul_eq_mul,mul_one,mul_comm]

lemma hi_gate (A D : Finset (I n)) (j : I n) (hB : 2 ≤ (others A j).card) : gate A j (hi A D j)=1 := by
  classical
  have hf : (others A j).filter (fun i => hi A D j i=true)=others A j := by
    apply filter_eq_self.mpr
    intro i him
    have h : i ∉ A ∧ i ≠ j := by simpa [others,and_comm] using him
    simp [hi,h.1,h.2]
  have hc : 2 ≤ count (others A j) (hi A D j) := by simpa [count,hf] using hB
  simp [gate,hi,hc]

/-- Exact loss formula for every selected set S. No cardinality premise on S
is needed for this identity; the k-budget is imposed by the game afterwards. -/
theorem actual_loss_formula (A T S : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjT : j ∉ T)
    (rho : ℝ) (hr : 1 ≤ rho) (hB : 2 ≤ (others A j).card) :
    productCompressionLoss (fibreWorld A T j rho) (productResponse corner (fibreWorld A T j rho)) S=
      (1+(A.card:ℝ)+rho*((T \ S).card:ℝ)-2*((A ∩ (T \ S)).card:ℝ))/2 := by
  classical
  let D := T \ S
  have hjD : j ∉ D := by simp [D,hjT]
  have hl : gate A j (lo A D j)+linear (compensation A D rho) (lo A D j)=-((A \ D).card:ℝ) := by
    rw [lo_linear A D j hjA hjD]
    simp [gate,lo]
  have hu : gate A j (hi A D j)+linear (compensation A D rho) (hi A D j)=
      1+rho*(D.card:ℝ)-((A ∩ D).card:ℝ) := by
    rw [hi_gate A D j hB,hi_linear A D j hjA hjD];ring
  have he := osc_of_extremes (fun x => gate A j x+linear (compensation A D rho) x)
    (lo A D j) (hi A D j) (fun x => by
      rw [hl]
      have h := linear_bounds A D rho hr x
      linarith [(gate_bounds A j x).1]) (fun x => by
      rw [hu]
      have h := linear_bounds A D rho hr x
      linarith [(gate_bounds A j x).2])
  unfold productCompressionLoss
  simp_rw [actual_residual A T S j hjA]
  change osc (fun x => gate A j x+linear (compensation A D rho) x)/2=_
  rw [he,hl,hu]
  have hc : ((A \ D).card:ℝ)+((A ∩ D).card:ℝ)=(A.card:ℝ) := by
    exact_mod_cast card_sdiff_add_card_inter A D
  change _=(1+(A.card:ℝ)+rho*(D.card:ℝ)-2*((A ∩ D).card:ℝ))/2
  linarith

#print axioms common_response
#print axioms mixed_unchanged
#print axioms actual_loss_formula
end
end CIGAMF.P13.D6SameResponseMarginLoss
