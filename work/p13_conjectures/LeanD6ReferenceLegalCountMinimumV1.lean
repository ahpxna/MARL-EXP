import «LeanD6ReferenceFullCountLossV1»

/-! # D04: exact minimum over all legal retained sets equals the feasible count grid.
The cardinality constraint is preserved. A count grid point is not merely a
formal alternative: its actual retained set is constructed using outside-T
filler. This is fixed-world decision optimization, not a minimax/WLOG theorem
about priors on hidden worlds or A-free randomized decisions.
-/
namespace CIGAMF.P13.D6ReferenceLegalCountMinimum
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.P13.D6ReferenceRetainedOscillation CIGAMF.P13.D6ReferenceFullCountLoss
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference CIGAMF.V4.SupportGeometry
noncomputable section
variable {n : ℕ}

theorem every_count_legal (A T : Finset (I n)) (j : I n)
    (hroom : 2*T.card ≤ Fintype.card (I n)) (u v : ℕ)
    (hu : u ≤ (T ∩ A).card) (hv : v ≤ (T ∩ others A j).card) :
    ∃ S : Finset (I n), S.card=T.card ∧
      ((T \ S) ∩ A).card=u ∧ ((T \ S) ∩ others A j).card=v := by
  classical
  obtain ⟨EA, hEA, hEAc⟩ := (T ∩ A).exists_subset_card_eq hu
  obtain ⟨EB, hEB, hEBc⟩ := (T ∩ others A j).exists_subset_card_eq hv
  have hDT : EA ∪ EB ⊆ T := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact (Finset.mem_inter.mp (hEA h)).1
    · exact (Finset.mem_inter.mp (hEB h)).1
  have hDA : (EA ∪ EB) ∩ A = EA := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hiA⟩
      · exact h
      · exact False.elim ((others_not_mem_A A j i (Finset.mem_inter.mp (hEB h)).2) hiA)
    · intro h
      exact ⟨Or.inl h, (Finset.mem_inter.mp (hEA h)).2⟩
  have hDB : (EA ∪ EB) ∩ others A j = EB := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨h | h, hiB⟩
      · exact False.elim ((others_not_mem_A A j i hiB) (Finset.mem_inter.mp (hEA h)).2)
      · exact h
    · intro h
      exact ⟨Or.inr h, (Finset.mem_inter.mp (hEB h)).2⟩
  obtain ⟨S, hSc, hSD⟩ := legal_count_realizable T (EA ∪ EB) hDT hroom
  refine ⟨S, hSc, ?_, ?_⟩
  · rw [hSD, hDA, hEAc]
  · rw [hSD, hDB, hEBc]

theorem omitted_count_le (T S E : Finset (I n)) : ((T \ S) ∩ E).card ≤ (T ∩ E).card := by
  apply Finset.card_le_card
  intro i hi
  have h := Finset.mem_inter.mp hi
  exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp h.1).1, h.2⟩

instance legalDecision_nonempty (T : Finset (I n)) :
    Nonempty {S : Finset (I n) // S.card=T.card} := ⟨⟨T,rfl⟩⟩

def legalMinimum (A T : Finset (I n)) (j : I n) (rho t : ℝ) : ℝ :=
  minVal (fun S : {S : Finset (I n) // S.card=T.card} =>
    productCompressionLoss (centeredWorld A T j rho t)
      (productResponse (bern t) (centeredWorld A T j rho t)) S.val)

def countMinimum (A T : Finset (I n)) (j : I n) (rho t : ℝ) : ℝ :=
  minVal (fun z : Fin ((T ∩ A).card+1) × Fin ((T ∩ others A j).card+1) =>
    countLoss (gateMass t A j) (slopeBval t A j) rho A.card (others A j).card z.1.val z.2.val)

/-- Equality of the two optimization problems, with both directions proved. -/
theorem actual_legal_minimum_eq_count_minimum (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (A T : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjT : j ∉ T)
    (hB2 : 2 ≤ (others A j).card) (rho : ℝ) (hr : 1 ≤ rho)
    (hroom : 2*T.card ≤ Fintype.card (I n)) :
    legalMinimum A T j rho t = countMinimum A T j rho t := by
  classical
  unfold legalMinimum countMinimum
  apply le_antisymm
  · apply le_minVal
    intro z
    obtain ⟨S, hSc, hA, hB⟩ := every_count_legal A T j hroom z.1.val z.2.val
      (by omega) (by omega)
    have h := minVal_le (fun R : {R : Finset (I n) // R.card=T.card} =>
      productCompressionLoss (centeredWorld A T j rho t)
        (productResponse (bern t) (centeredWorld A T j rho t)) R.val) ⟨S,hSc⟩
    rw [actual_full_count_loss t ht0 ht1 A T S j hjA hjT hB2 rho hr, hA, hB] at h
    exact h
  · apply le_minVal
    intro S
    let u : Fin ((T ∩ A).card+1) :=
      ⟨((T \ S.val) ∩ A).card, by have := omitted_count_le T S.val A; omega⟩
    let v : Fin ((T ∩ others A j).card+1) :=
      ⟨((T \ S.val) ∩ others A j).card, by have := omitted_count_le T S.val (others A j); omega⟩
    have h := minVal_le (fun z : Fin ((T ∩ A).card+1) × Fin ((T ∩ others A j).card+1) =>
      countLoss (gateMass t A j) (slopeBval t A j) rho A.card (others A j).card z.1.val z.2.val) (u,v)
    rw [actual_full_count_loss t ht0 ht1 A T S.val j hjA hjT hB2 rho hr]
    exact h

#print axioms every_count_legal
#print axioms omitted_count_le
#print axioms actual_legal_minimum_eq_count_minimum
end
end CIGAMF.P13.D6ReferenceLegalCountMinimum
