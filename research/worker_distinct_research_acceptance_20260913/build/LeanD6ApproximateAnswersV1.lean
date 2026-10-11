import «LeanD6ThresholdConstructionV1»
import Mathlib

/-! Approximate answers use actual geometric regret. Alternative nuisance,
not the true nuisance, determines whether an answer is wrong. -/
namespace CIGAMF.P13.D6ApproximateAnswers
open Finset
open CIGAMF.P13.D6Threshold
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

def exchange (A B : Finset (I n)) : ℕ := (A \ B).card

theorem complement_regret_exchange (A B : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hcard : Bᶜ.card = A.card) (hbal : Aᶜ.card = A.card)
    (hB : 2 ≤ (others A j).card) :
    productCompressionLoss (world A j mu) (productResponse corner (world A j mu)) Bᶜ -
      productCompressionLoss (world A j mu) (productResponse corner (world A j mu)) Aᶜ =
      (2-mu)*(exchange A B : ℝ)/2 := by
  rw [actual_regret A Bᶜ j hj mu hmu hmu1 hcard hbal hB]
  have he : Bᶜ ∩ A = A \ B := by ext i; simp [and_comm]
  rw [he]
  rfl

theorem epsilon_good_iff_exchange_ball (d : ℕ) (mu eps : ℝ)
    (hm : mu ≤ 1) (he : 0 ≤ eps) :
    (2-mu)*(d : ℝ)/2 ≤ eps ↔ d ≤ ⌊2*eps/(2-mu)⌋₊ := by
  have hp : 0 < 2-mu := by linarith
  rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hp]
  constructor <;> intro h <;> nlinarith

theorem low_tolerance_zero_exchange (d : ℕ) (mu eps : ℝ)
    (hm : mu ≤ 1) (he : 0 ≤ eps) (he1 : eps < (2-mu)/2) :
    (2-mu)*(d : ℝ)/2 ≤ eps ↔ d=0 := by
  constructor
  · intro h
    by_contra hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd)
    have hp : 0 < 2-mu := by linarith
    nlinarith
  · intro h; simp [h,he]

theorem zero_exchange_iff_equal (A B : Finset (I n)) (hc : A.card = B.card) :
    exchange A B = 0 ↔ A=B := by
  simp only [exchange, card_eq_zero, sdiff_eq_empty_iff_subset]
  constructor
  · intro h; exact eq_of_subset_of_card_le h hc.ge
  · intro h; simp [h]

def BadNuisance (d : ℕ) (eps nu : ℝ) : Prop :=
  0 ≤ nu ∧ nu ≤ 1 ∧ eps < (2-nu)*(d : ℝ)/2

theorem bad_nuisance_interval (d : ℕ) (hd : 0 < d) (eps nu : ℝ) :
    BadNuisance d eps nu ↔ 0 ≤ nu ∧ nu ≤ 1 ∧ nu < 2-2*eps/(d : ℝ) := by
  have hp : (0 : ℝ) < d := by exact_mod_cast hd
  unfold BadNuisance
  constructor
  · rintro ⟨h0,h1,hb⟩
    refine ⟨h0,h1,?_⟩
    rw [lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', div_lt_iff₀ hp]
    nlinarith
  · rintro ⟨h0,h1,hb⟩
    refine ⟨h0,h1,?_⟩
    rw [lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', div_lt_iff₀ hp] at hb
    nlinarith

theorem bad_nuisance_nonempty (d : ℕ) (eps : ℝ) (he : 0 ≤ eps) :
    (∃ nu, BadNuisance d eps nu) ↔ eps < (d : ℝ) := by
  constructor
  · rintro ⟨nu,h0,h1,hb⟩
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [mul_nonneg h0 hd]
  · intro h
    exact ⟨0, by norm_num [BadNuisance]; linarith⟩

theorem bad_zero_distance (eps nu : ℝ) (he : 0 ≤ eps) : ¬ BadNuisance 0 eps nu := by
  simp [BadNuisance, not_lt.mpr he]

theorem bad_subset_exact (d : ℕ) (eps nu : ℝ) (he : 0 ≤ eps)
    (h : BadNuisance d eps nu) : BadNuisance d 0 nu := by
  exact ⟨h.1,h.2.1,lt_of_le_of_lt he h.2.2⟩

#print axioms complement_regret_exchange
#print axioms epsilon_good_iff_exchange_ball
#print axioms low_tolerance_zero_exchange
#print axioms zero_exchange_iff_equal
#print axioms bad_nuisance_interval
#print axioms bad_nuisance_nonempty
#print axioms bad_zero_distance
#print axioms bad_subset_exact
end
end CIGAMF.P13.D6ApproximateAnswers
