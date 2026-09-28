import «LeanD6BernoulliSlopeV1»

/-! # The third reference slope: a coordinate of the `others A j` block.

Kept in its own module so a failure here cannot cost the two slopes already
proved in `LeanD6BernoulliSlopeV1`.

The exponent here is `|A| + |B| - 1`, NOT `|A| + |B|`. In the 2k-coordinate
instance (`|A| = k`, `|B| = k - 1`) both spellings happen to agree with
`b = c*(k-2)*t`, so the error is invisible there; it shows up only when the two
block sizes are varied independently. The statement below was checked exactly
against this corpus's own `gate` at ten independent (|A|, |B|, t) settings.
-/

namespace CIGAMF.P13.D6ReferenceSlopeB
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge CIGAMF.P13.D6ReferenceTail
open CIGAMF.P13.D6ReferenceSlope
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

theorem slope_at_B (t : ℝ) (A : Finset (I n)) (j : I n) (hjA : j ∉ A) (i : I n)
    (hiB : i ∈ others A j) (hB2 : 2 ≤ (others A j).card) :
    productResponse (bern t) (gate A j) i true
      -productResponse (bern t) (gate A j) i false
      = (((others A j).card:ℝ)-1)*t*(1-t)^(A.card+(others A j).card-1) := by
  classical
  set B := others A j with hBdef
  have hij : i ≠ j := Finset.ne_of_mem_erase hiB
  have hiA : i ∉ A := (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hiB)).2
  have hjB : j ∉ B := by simp [hBdef, others]
  have hkey : ∀ (u : Bool) (c : I n → Bool),
      (1-bit (Function.update c i u j))
        *(1-offProd A (Function.update c i u)*leOne B (Function.update c i u))
      = (1-bit (c j))*(1-offProd A c*leOne B (Function.update c i u)) := by
    intro u c
    rw [Function.update_of_ne (Ne.symm hij), offProd_update_not_mem A i hiA u c]
  rw [gate_response, gate_response]
  rw [← hBdef]
  simp_rw [hkey, leOne_update_true_mem B i hiB, leOne_update_false_mem B i hiB]
  -- the two responses now differ only through `offProd (B.erase i)` vs `leOne (B.erase i)`
  have hsing : ∀ c : I n → Bool, (1-bit (c j))=offProd {j} c := by
    intro c; unfold offProd; simp
  have hdjA : Disjoint ({j} : Finset (I n)) A := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at ha
    subst ha
    exact hjA hb
  have hjoin : ∀ c : I n → Bool,
      (1-bit (c j))*offProd A c=offProd (insert j A) c := by
    intro c
    rw [hsing c, offProd_union {j} A hdjA c]
    congr 1
  have hSB : Disjoint (insert j A) (B.erase i) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have haB : a ∈ B := Finset.mem_of_mem_erase hb
    rcases Finset.mem_insert.mp ha with h|h
    · subst h; exact hjB haB
    · exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase haB)).2 h
  have hcardS : (insert j A).card=A.card+1 := Finset.card_insert_of_notMem hjA
  have hcardE : (B.erase i).card=B.card-1 := Finset.card_erase_of_mem hiB
  have hB1 : 1 ≤ (B.erase i).card := by rw [hcardE]; omega
  -- expand the difference of the two expectations
  rw [show (fun c : I n → Bool => (1-bit (c j))*(1-offProd A c*offProd (B.erase i) c))
        = (fun c : I n → Bool =>
            (1-bit (c j))-(1-bit (c j))*offProd A c*offProd (B.erase i) c) from
      funext (fun c => by ring)]
  rw [show (fun c : I n → Bool => (1-bit (c j))*(1-offProd A c*leOne (B.erase i) c))
        = (fun c : I n → Bool =>
            (1-bit (c j))-(1-bit (c j))*offProd A c*leOne (B.erase i) c) from
      funext (fun c => by ring)]
  rw [expect_sub (bern t) (fun c => 1-bit (c j))
      (fun c => (1-bit (c j))*offProd A c*offProd (B.erase i) c),
    expect_sub (bern t) (fun c => 1-bit (c j))
      (fun c => (1-bit (c j))*offProd A c*leOne (B.erase i) c)]
  simp_rw [hjoin]
  rw [show (fun c : I n → Bool => offProd (insert j A) c*offProd (B.erase i) c)
        = (offProd ((insert j A) ∪ (B.erase i)) : (I n → Bool) → ℝ) from
      funext (fun c => offProd_union (insert j A) (B.erase i) hSB c)]
  rw [expect_offProd t ((insert j A) ∪ (B.erase i)),
    expect_offProd_mul_leOne t (insert j A) (B.erase i) hSB hB1,
    Finset.card_union_of_disjoint hSB, hcardS, hcardE]
  -- pure arithmetic from here
  obtain ⟨m, hm⟩ : ∃ m, B.card=m+2 := ⟨B.card-2, by omega⟩
  rw [hm]
  simp only [show m+2-1=m+1 by omega, show A.card+1+(m+1)=A.card+m+2 by omega,
    show A.card+(m+2)-1=A.card+m+1 by omega, pow_succ, pow_add]
  push_cast
  ring

#print axioms slope_at_B

end
end CIGAMF.P13.D6ReferenceSlopeB
