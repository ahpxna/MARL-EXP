import Mathlib

/-! Finite translates give a balanced query design with exactly |C| rows.
Rows may overlap: no unknown world or hidden label enters the construction. -/
namespace CIGAMF.P13.BalancedTranslateDesign
open scoped BigOperators
open Finset
noncomputable section
variable {C : Type*} [Fintype C] [DecidableEq C] [AddCommGroup C]

def row (Q : Finset C) (t : C) : Finset C :=
  univ.filter (fun i => i - t ∈ Q)

@[simp] theorem mem_row (Q : Finset C) (t i : C) :
    i ∈ row Q t ↔ i - t ∈ Q := by simp [row]

theorem row_card (Q : Finset C) (t : C) : (row Q t).card = Q.card := by
  apply card_bij (fun i _ => i - t)
  · intro i hi; exact (mem_row Q t i).mp hi
  · intro i hi j hj hij; exact sub_left_injective hij
  · intro i hi
    refine ⟨i + t, ?_, ?_⟩ <;> simp [hi]

theorem column_sum (Q : Finset C) (i : C) :
    (∑ t : C, if i ∈ row Q t then (1 : ℝ) else 0) = Q.card := by
  simp only [mem_row]
  have hb : Function.Bijective (fun t : C => i - t) := by
    constructor
    · intro a b h; exact sub_right_injective h
    · intro a; exact ⟨i - a, by abel⟩
  rw [hb.sum_comp (fun x => if x ∈ Q then (1 : ℝ) else 0)]
  simp

theorem intersection_sum (Q B : Finset C) :
    (∑ t : C, ((row Q t ∩ B).card : ℝ)) = (Q.card : ℝ) * B.card := by
  have he (t : C) : ((row Q t ∩ B).card : ℝ) =
      ∑ i ∈ B, if i ∈ row Q t then (1 : ℝ) else 0 := by
    have hf : B.filter (fun i => i ∈ row Q t) = row Q t ∩ B := by
      ext i; simp [and_comm]
    simp [← hf]
  simp_rw [he]
  rw [sum_comm]
  simp_rw [column_sum]
  simp [mul_comm]

#print axioms row_card
#print axioms column_sum
#print axioms intersection_sum
end
end CIGAMF.P13.BalancedTranslateDesign
