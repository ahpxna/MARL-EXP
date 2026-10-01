import «LeanD6ThresholdConstructionV1»

/-! A direct witness throughout the formerly missing margin interval (1,2).
The common statement here compares Top-C with a feasible complement; it does
not assume or assert that complement is globally optimal. This suffices for
strict failure below 2. Reference is explicitly the corner product reference. -/
namespace CIGAMF.P13.D6SharpMarginSteering
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference CIGAMF.V4.SupportGeometry
noncomputable section
variable {n : ℕ}

def bump (A : Finset (I n)) (rho : ℝ) (i : I n) : ℝ := if i ∈ A then rho-1 else 0
def steered (A : Finset (I n)) (j : I n) (rho : ℝ) (x : I n → Bool) : ℝ :=
  world A j 1 x+linear (bump A rho) x

lemma bump_sum (A : Finset (I n)) (rho : ℝ) (x : I n → Bool) :
    linear (bump A rho) x=(rho-1)*∑ i ∈ A,bit (x i) := by
  classical
  simp [linear,bump,ite_mul,← mul_sum]

lemma world_one_gate (A : Finset (I n)) (j : I n) (x : I n → Bool) :
    world A j 1 x=gate A j x := by simp [world,linear,coeff]

/-- Full responses, not just their oscillations. -/
theorem steered_response (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (rho : ℝ) (i : I n) (u : Bool) :
    productResponse corner (steered A j rho) i u=(if i ∈ A then rho else 0)*bit u := by
  rw [corner_response]
  have hw := world_response A j hj 1 i u
  rw [corner_response] at hw
  have hl := linear_difference (bump A rho) zero i u false
  rw [show Function.update (zero : I n → Bool) i false=zero from Function.update_eq_self i zero,
    linear_zero,bit_false] at hl
  simp only [sub_zero] at hl
  dsimp only [steered]
  rw [hw,hl]
  by_cases hi : i ∈ A <;> simp [D6Threshold.slope,bump,hi] <;> ring

theorem steered_span (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (rho : ℝ) (hr : 0 ≤ rho) (i : I n) :
    osc (productResponse corner (steered A j rho) i)=if i ∈ A then rho else 0 := by
  have he : productResponse corner (steered A j rho) i=
      fun u => (if i ∈ A then rho else 0)*bit u := by
    funext u; exact steered_response A j hj rho i u
  rw [he]
  apply osc_bit_nonneg
  split <;> linarith

theorem steered_is_top (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (rho : ℝ) (hr : 0 ≤ rho) :
    IsTopKByScore (fun i => osc (productResponse corner (steered A j rho) i)) A A.card := by
  have he : (fun i => osc (productResponse corner (steered A j rho) i))=
      fun i => if i ∈ A then rho else 0 := by funext i; exact steered_span A j hj rho hr i
  rw [he]
  refine ⟨rfl,?_⟩
  intro S hS
  have ha : (∑ i ∈ A,if i ∈ A then rho else 0)=(A.card:ℝ)*rho := by simp
  rw [ha]
  calc _ ≤ ∑ _i ∈ S,rho := by
         apply sum_le_sum; intro i _; split <;> linarith
       _ = _ := by simp [hS]

theorem steered_margin (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (rho : ℝ) (hr : 0 ≤ rho) (a b : I n) (ha : a ∈ A) (hb : b ∉ A) :
    osc (productResponse corner (steered A j rho) a)-
      osc (productResponse corner (steered A j rho) b)=rho := by
  rw [steered_span A j hj rho hr a,steered_span A j hj rho hr b]
  simp [ha,hb]

/-- Modular steering changes no mixed difference. -/
theorem steered_mixed (A : Finset (I n)) (j i : I n) (rho : ℝ) (x c : I n → Bool) :
    mixedDifference (steered A j rho) i x c=mixedDifference (world A j 1) i x c := by
  have hx := linear_difference (bump A rho) x i (x i) (c i)
  have hc := linear_difference (bump A rho) c i (x i) (c i)
  rw [Function.update_eq_self] at hx
  rw [Function.update_eq_self] at hc
  unfold mixedDifference steered
  linarith

theorem steered_mixed_bound (A : Finset (I n)) (j i : I n) (rho : ℝ) (x c : I n → Bool) :
    |mixedDifference (steered A j rho) i x c| ≤ 1 := by
  rw [steered_mixed]
  exact mixed_bound A j 1 i x c

theorem steered_mixed_attained (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (rho : ℝ) (a : I n) (ha : a ∈ A) :
    ∃ x c : I n → Bool,mixedDifference (steered A j rho) a x c=1 := by
  obtain ⟨x,c,h⟩ := mixed_bound_attained A j hj 1 a ha
  exact ⟨x,c,by rw [steered_mixed];exact h⟩

/-- The selected residual is unchanged by steering its own components. -/
lemma selected_residual (A : Finset (I n)) (j : I n) (hj : j ∉ A) (rho : ℝ) (x : I n → Bool) :
    steered A j rho x-∑ i ∈ A,productResponse corner (steered A j rho) i (x i)=
      world A j 1 x-∑ i ∈ A,productResponse corner (world A j 1) i (x i) := by
  simp_rw [steered_response A j hj,world_response A j hj]
  simp only [steered,bump_sum]
  have hs : ∑ i ∈ A,(if i ∈ A then rho else 0)*bit (x i)=rho*∑ i ∈ A,bit (x i) := by
    simp [← mul_sum]
  have ht : ∑ i ∈ A,slope A j 1 i*bit (x i)=∑ i ∈ A,bit (x i) := by
    apply sum_congr rfl
    intro i hi
    simp [D6Threshold.slope,hi]
  rw [hs,ht]
  ring

theorem steered_top_loss (A : Finset (I n)) (j : I n) (hj : j ∉ A) (rho : ℝ)
    (hbal : Aᶜ.card=A.card) (hB : 2 ≤ (others A j).card) :
    productCompressionLoss (steered A j rho) (productResponse corner (steered A j rho)) A=
      (1+(A.card:ℝ))/2 := by
  have he : productCompressionLoss (steered A j rho) (productResponse corner (steered A j rho)) A=
      productCompressionLoss (world A j 1) (productResponse corner (world A j 1)) A := by
    unfold productCompressionLoss
    simp_rw [selected_residual A j hj]
  rw [he,actual_loss A A j hj 1 (by norm_num) (by norm_num) rfl hbal hB]
  norm_num

/-- Every value of the steered function lies in this interval. -/
lemma steered_bounds (A : Finset (I n)) (j : I n) (rho : ℝ) (hr : 1 ≤ rho) (x : I n → Bool) :
    0 ≤ steered A j rho x ∧ steered A j rho x ≤ 1+(rho-1)*(A.card:ℝ) := by
  have hg := gate_bounds A j x
  have hs0 : 0 ≤ ∑ i ∈ A,bit (x i) := sum_nonneg (fun i _ => (bit_bounds _).1)
  have hs1 : ∑ i ∈ A,bit (x i) ≤ (A.card:ℝ) := by
    calc _ ≤ ∑ _i ∈ A,(1:ℝ) := sum_le_sum (fun i _ => (bit_bounds _).2)
         _ = _ := by simp
  rw [steered,world_one_gate,bump_sum]
  constructor
  · exact add_nonneg hg.1 (mul_nonneg (sub_nonneg.mpr hr) hs0)
  · nlinarith [mul_le_mul_of_nonneg_left hs1 (sub_nonneg.mpr hr)]

theorem complement_loss_upper (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (rho : ℝ) (hr : 1 ≤ rho) :
    productCompressionLoss (steered A j rho) (productResponse corner (steered A j rho)) Aᶜ ≤
      (1+(rho-1)*(A.card:ℝ))/2 := by
  classical
  have hzero (x : I n → Bool) : ∑ i ∈ Aᶜ,productResponse corner (steered A j rho) i (x i)=0 := by
    apply sum_eq_zero
    intro i hi
    rw [steered_response A j hj]
    simp [(mem_compl.mp hi)]
  unfold productCompressionLoss
  simp_rw [hzero,sub_zero]
  have hlo := le_minVal (steered A j rho) (fun x => (steered_bounds A j rho hr x).1)
  have hhi := maxVal_le (steered A j rho) (fun x => (steered_bounds A j rho hr x).2)
  unfold osc
  linarith

/-- A positive actual loss separation for every margin 1 <= rho < 2.
This supplies the lower-bound side of a proposed sharp threshold, without
an LP heuristic or enumeration over dimensions. No universal sufficiency
theorem at margin 2 is asserted by this module. -/
theorem sharp_margin_witness (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (rho : ℝ) (hr : 1 ≤ rho) (hbal : Aᶜ.card=A.card) (hB : 2 ≤ (others A j).card) :
    (A.card:ℝ)*(2-rho)/2 ≤
      productCompressionLoss (steered A j rho) (productResponse corner (steered A j rho)) A-
      productCompressionLoss (steered A j rho) (productResponse corner (steered A j rho)) Aᶜ := by
  rw [steered_top_loss A j hj rho hbal hB]
  have h := complement_loss_upper A j hj rho hr
  nlinarith

#print axioms steered_is_top
#print axioms steered_margin
#print axioms steered_mixed_attained
#print axioms steered_response
#print axioms steered_mixed_bound
#print axioms steered_top_loss
#print axioms sharp_margin_witness
end
end CIGAMF.P13.D6SharpMarginSteering
