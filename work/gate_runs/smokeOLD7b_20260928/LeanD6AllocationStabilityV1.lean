import «LeanD6GaussianQueryDominanceV1»
import «LeanD6AllocationRiskBridgeV1»

/-! Uniform stability in the true margin for every actual legal allocation.
This supports value tracking even when the set of optimal allocations jumps.
It is a deterministic ingredient, not a consistency or stopping-rate theorem. -/
namespace CIGAMF.P13.D6AllocationStability
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6AllocationRiskBridge
open CIGAMF.P13.D6AllocationFiniteBridge
noncomputable section
variable {n : ℕ}

lemma offset_bound (A : Finset (I n)) (j : I n) (q : ℝ) (hq : 1 ≤ q)
    (e : Measurement n) (he : Legal j q e) : |meanOffset A j e| ≤ q+1 := by
  cases e with
  | inl i => simp only [meanOffset]; split_ifs <;> norm_num <;> linarith
  | inr p =>
    have hc : (0:ℝ) ≤ (p.1 ∩ others A j).card := by positivity
    have hcu0 : ((p.1 ∩ others A j).card:ℝ) ≤ p.1.card := by exact_mod_cast card_le_card inter_subset_left
    have hcu : ((p.1 ∩ others A j).card:ℝ) ≤ q := hcu0.trans he.2.1
    rcases p with ⟨G,h⟩
    cases h <;> simp only [meanOffset,Bool.false_eq_true,↓reduceIte,bit_false,bit_true] <;>
      apply abs_le.mpr <;> constructor <;> linarith

lemma slope_bound (A : Finset (I n)) (j : I n) (q : ℝ) (hq : 1 ≤ q)
    (e : Measurement n) (he : Legal j q e) : |meanSlope A j e| ≤ q := by
  have hs := actual_mean_slope_bound A j q hq e he
  have ha := sq_abs (meanSlope A j e)
  nlinarith [abs_nonneg (meanSlope A j e)]

lemma actual_mean_bound (A : Finset (I n)) (j : I n) (q mu : ℝ) (hq : 1 ≤ q)
    (hj : j ∉ A) (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (e : Measurement n) (he : Legal j q e) :
    |actualMean A j mu e| ≤ 2*q+1 := by
  rw [actual_mean_affine A j hj q mu e he]
  have ho := offset_bound A j q hq e he
  have hs := slope_bound A j q hq e he
  calc
    _ ≤ |meanOffset A j e|+|meanSlope A j e*mu| := abs_add_le _ _
    _ = |meanOffset A j e|+|meanSlope A j e| *mu := by rw [abs_mul,abs_of_nonneg hm]
    _ ≤ 2*q+1 := by nlinarith [mul_le_mul_of_nonneg_right hs hm]

lemma actual_mean_stability (A : Finset (I n)) (j : I n) (q mu mhat : ℝ) (hq : 1 ≤ q)
    (hj : j ∉ A) (e : Measurement n) (he : Legal j q e) :
    |actualMean A j mu e-actualMean A j mhat e| ≤ q*|mu-mhat| := by
  rw [actual_mean_affine A j hj q mu e he,actual_mean_affine A j hj q mhat e he]
  have hid : meanOffset A j e+meanSlope A j e*mu-(meanOffset A j e+meanSlope A j e*mhat)=
      meanSlope A j e*(mu-mhat) := by ring
  rw [hid,abs_mul]
  exact mul_le_mul_of_nonneg_right (slope_bound A j q hq e he) (abs_nonneg _)

/-- Uniform over the entire nuisance interval and the literal query library. -/
theorem actual_information_stability (A A' : Finset (I n)) (j : I n) (q mu mhat nu : ℝ)
    (hq : 1 ≤ q) (hj : j ∉ A) (hj' : j ∉ A')
    (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (hh : 0 ≤ mhat) (hh1 : mhat ≤ 1)
    (hn : 0 ≤ nu) (hn1 : nu ≤ 1) (e : Measurement n) (he : Legal j q e) :
    |information A A' j mu nu e-information A A' j mhat nu e| ≤
      2*q*(2*q+1)*|mu-mhat| := by
  have info (x : ℝ) : information A A' j x nu e=
      (actualMean A j x e-actualMean A' j nu e)^2/2 := by cases e <;> rfl
  rw [info mu,info mhat]
  let a := actualMean A j mu e-actualMean A' j nu e
  let b := actualMean A j mhat e-actualMean A' j nu e
  have hma := actual_mean_bound A j q mu hq hj hm hm1 e he
  have hmb := actual_mean_bound A j q mhat hq hj hh hh1 e he
  have hmc := actual_mean_bound A' j q nu hq hj' hn hn1 e he
  have ha : |a| ≤ 2*(2*q+1) := by
    have ht : |a| ≤ |actualMean A j mu e|+|actualMean A' j nu e| := by
      simpa [a] using abs_sub_le (actualMean A j mu e) 0 (actualMean A' j nu e)
    linarith only [ht,hma,hmc]
  have hb : |b| ≤ 2*(2*q+1) := by
    have ht : |b| ≤ |actualMean A j mhat e|+|actualMean A' j nu e| := by
      simpa [b] using abs_sub_le (actualMean A j mhat e) 0 (actualMean A' j nu e)
    linarith only [ht,hmb,hmc]
  have hab : |a-b| ≤ q*|mu-mhat| := by
    dsimp [a,b]
    simpa only [sub_sub_sub_cancel_right] using actual_mean_stability A j q mu mhat hq hj e he
  have hsum : |a+b| ≤ 4*(2*q+1) := by linarith [abs_add_le a b]
  have hprod := mul_le_mul hab hsum (abs_nonneg (a+b)) (by positivity : 0 ≤ q*|mu-mhat|)
  change |a^2/2-b^2/2| ≤ _
  have hid : a^2/2-b^2/2=(a-b)*(a+b)/2 := by ring
  rw [hid,abs_div,abs_mul]
  norm_num
  nlinarith only [hprod]

/-- Convex allocation averages inherit the same constant, independent of how
many actual queries the allocation uses. -/
theorem weighted_information_stability (A A' : Finset (I n)) (j : I n) (q mu mhat nu : ℝ)
    (hq : 1 ≤ q) (hj : j ∉ A) (hj' : j ∉ A')
    (hm : 0 ≤ mu) (hm1 : mu ≤ 1) (hh : 0 ≤ mhat) (hh1 : mhat ≤ 1)
    (hn : 0 ≤ nu) (hn1 : nu ≤ 1)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e) (hnorm : ∑ e ∈ E,w e=1) :
    |(∑ e ∈ E,w e*information A A' j mu nu e)-(∑ e ∈ E,w e*information A A' j mhat nu e)| ≤
      2*q*(2*q+1)*|mu-mhat| := by
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ e ∈ E,|w e*information A A' j mu nu e-w e*information A A' j mhat nu e| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ E,w e*(2*q*(2*q+1)*|mu-mhat|) := by
      apply sum_le_sum
      intro e he
      rw [← mul_sub,abs_mul,abs_of_nonneg (hw e he)]
      exact mul_le_mul_of_nonneg_left
        (actual_information_stability A A' j q mu mhat nu hq hj hj' hm hm1 hh hh1 hn hn1 e (hl e he))
        (hw e he)
    _ = _ := by rw [← sum_mul,hnorm,one_mul]

#print axioms actual_mean_bound
#print axioms actual_mean_stability
#print axioms actual_information_stability
#print axioms weighted_information_stability
end
end CIGAMF.P13.D6AllocationStability
