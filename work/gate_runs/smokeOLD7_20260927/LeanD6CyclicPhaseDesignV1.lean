import «LeanBalancedTranslateDesignV1»
import «LeanD6BlindPhaseBlocksV1»

/-! A-free phase observations from |U| translates of a q-subset of U.
The rows are actual legal D6 off queries, with |U|=2q+1. -/
namespace CIGAMF.P13.D6CyclicPhaseDesign
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance
open CIGAMF.P13.BalancedTranslateDesign
noncomputable section
variable {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C] [AddCommGroup C]

abbrev Coordinates (j : I n) := {i : I n // i ≠ j}

def actualRow {j : I n} (e : C ≃ Coordinates j) (Q : Finset C) (t : C) : Finset (I n) :=
  (row Q t).image (fun x => (e x).val)

def encoded {j : I n} (e : C ≃ Coordinates j) (B : Finset (I n)) : Finset C :=
  univ.filter (fun x => (e x).val ∈ B)

lemma coordinate_injective {j : I n} (e : C ≃ Coordinates j) :
    Function.Injective (fun x => (e x).val) := Subtype.val_injective.comp e.injective

theorem actualRow_card {j : I n} (e : C ≃ Coordinates j) (Q : Finset C) (t : C) :
    (actualRow e Q t).card = Q.card := by
  rw [actualRow, card_image_of_injective _ (coordinate_injective e), row_card]

theorem actualRow_legal {j : I n} (e : C ≃ Coordinates j) (Q : Finset C)
    (q : ℕ) (hq : 3 ≤ q) (hQ : Q.card = q) (t : C) :
    Legal j q (.inr (actualRow e Q t, false)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨x, hx, he⟩ := mem_image.mp h
    exact (e x).property he
  · rw [actualRow_card, hQ]
  · intro _; rw [actualRow_card, hQ]; omega

lemma encoded_card {j : I n} (e : C ≃ Coordinates j) (B : Finset (I n))
    (hj : j ∉ B) : (encoded e B).card = B.card := by
  apply card_bij (fun x _ => (e x).val)
  · intro x hx; exact (mem_filter.mp hx).2
  · intro x hx y hy h; exact coordinate_injective e h
  · intro i hi
    have hij : i ≠ j := by intro h; subst i; exact hj hi
    refine ⟨e.symm ⟨i,hij⟩, ?_, ?_⟩ <;> simp [encoded,hi]

lemma actual_inter_card {j : I n} (e : C ≃ Coordinates j)
    (Q : Finset C) (t : C) (B : Finset (I n)) :
    (actualRow e Q t ∩ B).card = (row Q t ∩ encoded e B).card := by
  have he : (row Q t ∩ encoded e B).image (fun x => (e x).val) = actualRow e Q t ∩ B := by
    ext i
    constructor
    · intro hi
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hi
      exact mem_inter.mpr ⟨mem_image.mpr ⟨x,(mem_inter.mp hx).1,rfl⟩,
        (mem_filter.mp (mem_inter.mp hx).2).2⟩
    · intro hi
      obtain ⟨x,hx,he⟩ := mem_image.mp (mem_inter.mp hi).1
      refine mem_image.mpr ⟨x,mem_inter.mpr ⟨hx,?_⟩,he⟩
      simp only [encoded,mem_filter,mem_univ,true_and]
      rw [he]; exact (mem_inter.mp hi).2
  rw [← he,card_image_of_injective _ (coordinate_injective e)]

theorem actual_intersection_sum {j : I n} (e : C ≃ Coordinates j)
    (Q : Finset C) (B : Finset (I n)) (hj : j ∉ B) :
    (∑ t : C, ((actualRow e Q t ∩ B).card : ℝ)) = (Q.card : ℝ) * B.card := by
  simp_rw [actual_inter_card]
  rw [intersection_sum, encoded_card e B hj]

theorem actual_mean_sum {j : I n} (e : C ≃ Coordinates j) (Q : Finset C)
    (q : ℕ) (hq : 3 ≤ q) (hQ : Q.card = q)
    (A : Finset (I n)) (hj : j ∉ A) (hB : (others A j).card=q) (mu : ℝ) :
    (∑ t : C, actualMean A j mu (.inr (actualRow e Q t,false))) =
      Fintype.card C + (q:ℝ)^2*(1-mu) := by
  have hm (t : C) : actualMean A j mu (.inr (actualRow e Q t,false)) =
      1 + ((actualRow e Q t ∩ others A j).card:ℝ)*(1-mu) := by
    rw [actual_mean_affine A j hj q mu _ (actualRow_legal e Q q hq hQ t)]
    simp only [meanOffset,meanSlope,Bool.false_eq_true,↓reduceIte,
      CIGAMF.P13.D6Threshold.bit_false,sub_zero]
    ring
  simp_rw [hm]
  rw [sum_add_distrib, ← sum_mul,
    actual_intersection_sum e Q (others A j) (by simp [others]), hQ,hB]
  simp [pow_two]

/-- The coordinate system and all rows are selected before A and mu are given. -/
theorem design_exists (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1)) :
    ∃ G : ZMod (2*q+1) → Finset (I (2*q+1)),
      (∀ t, Legal j q (.inr (G t,false)) ∧ (G t).card=q) ∧
      ∀ A : Finset (I (2*q+1)), j ∉ A → (others A j).card=q → ∀ mu : ℝ,
        (∑ t, actualMean A j mu (.inr (G t,false))) =
          (2*(q:ℝ)+1)+(q:ℝ)^2*(1-mu) := by
  have hn : 0 < 2*q+1 := by omega
  letI : NeZero (2*q+1) := ⟨by omega⟩
  have hc : Fintype.card (ZMod (2*q+1)) = Fintype.card (Coordinates j) := by
    have he : (univ : Finset (I (2*q+1))).filter (fun i => i ≠ j) = univ.erase j := by
      ext i; simp [and_comm]
    simp [Coordinates,Fintype.card_subtype,he,I]
  let e : ZMod (2*q+1) ≃ Coordinates j := Fintype.equivOfCardEq hc
  obtain ⟨Q,hsub,hQ⟩ := exists_subset_card_eq (s := (univ : Finset (ZMod (2*q+1))))
    (n := q) (by simp; omega)
  refine ⟨actualRow e Q, ?_, ?_⟩
  · intro t
    exact ⟨actualRow_legal e Q q hq hQ t,by rw [actualRow_card,hQ]⟩
  · intro A hj hB mu
    simpa using actual_mean_sum e Q q hq hQ A hj hB mu

#print axioms actualRow_legal
#print axioms actual_intersection_sum
#print axioms actual_mean_sum
#print axioms design_exists
end
end CIGAMF.P13.D6CyclicPhaseDesign
