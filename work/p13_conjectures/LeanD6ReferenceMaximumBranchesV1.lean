import «LeanD6ReferenceRetainedOscillationV1»

/-! # D04: the two exceptional maximum branches.
The count identity is on actual cube points. The empty omitted set and the
singleton-B omitted set are treated explicitly, with attaining cube witnesses.
-/
namespace CIGAMF.P13.D6ReferenceMaximumBranches
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge CIGAMF.P13.D6ReferenceTail
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.P13.D6ReferenceRetainedOscillation
open CIGAMF.V4.SupportGeometry
noncomputable section
variable {n : ℕ}

theorem sum_bits (E : Finset (I n)) (x : I n → Bool) :
    (∑ i ∈ E, bit (x i)) = (count E x : ℝ) := by
  simp [bit, count]

theorem count_hiPoint (E D : Finset (I n)) : count E (hiPoint D) = (E ∩ D).card := by
  simp [count, hiPoint, Finset.filter_mem_eq_inter]

theorem core_counts (t : ℝ) (A D : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (hjD : j ∉ D) (rho : ℝ) (x : I n → Bool) :
    core A D j rho t x = gate A j x+(1-gateMass t A j)*bit (x j)
      +rho*(count D x : ℝ)-gateMass t A j*(count A x : ℝ)
      -slopeBval t A j*(count (others A j) x : ℝ) := by
  classical
  have he : ∀ i, retainedCoeff A D j rho t i*bit (x i) =
      (if i = j then (1-gateMass t A j)*bit (x j) else 0)
      +(if i ∈ D then rho*bit (x i) else 0)
      -(if i ∈ A then gateMass t A j*bit (x i) else 0)
      -(if i ∈ others A j then slopeBval t A j*bit (x i) else 0) := by
    intro i
    by_cases hij : i = j
    · subst i
      simp [retainedCoeff, gateSlope, hjA, hjD, mem_others_iff]
    · by_cases hiA : i ∈ A <;> by_cases hiD : i ∈ D <;>
        simp [retainedCoeff, gateSlope, hij, hiA, hiD, mem_others_iff] <;> ring
  have hl : linear (retainedCoeff A D j rho t) x =
      (1-gateMass t A j)*bit (x j)+rho*(count D x : ℝ)
      -gateMass t A j*(count A x : ℝ)-slopeBval t A j*(count (others A j) x : ℝ) := by
    unfold linear
    simp_rw [he]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp [Finset.sum_ite_mem, ← Finset.mul_sum, sum_bits]
  rw [core, hl]
  ring

theorem count_ge_one (E : Finset (I n)) (x : I n → Bool)
    (h : ∃ i ∈ E, x i = true) : 1 ≤ count E x := by
  obtain ⟨i, hi, hx⟩ := h
  exact Finset.card_pos.mpr ⟨i, by simp [hi, hx]⟩

theorem bit_le_count (E : Finset (I n)) (i : I n) (hi : i ∈ E) (x : I n → Bool) :
    bit (x i) ≤ (count E x : ℝ) := by
  cases hx : x i
  · simp only [bit_false]; positivity
  · simp only [bit_true]
    exact_mod_cast count_ge_one E x ⟨i, hi, hx⟩

/-- The distinguished singleton turns the gate off and attains 1-a. -/
theorem core_at_j (A D : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjD : j ∉ D)
    (rho t : ℝ) : core A D j rho t (hiPoint {j}) = 1-gateMass t A j := by
  rw [core_counts t A D j hjA hjD rho]
  simp_rw [count_hiPoint]
  simp [gate, hiPoint, hjA, hjD, mem_others_iff, bit]

/-- A pair of B coordinates turns the gate on. -/
theorem core_at_B_pair (t : ℝ) (A D : Finset (I n)) (j i l : I n)
    (hjA : j ∉ A) (hjD : j ∉ D) (hi : i ∈ others A j)
    (hl : l ∈ others A j) (hil : i ≠ l) (rho : ℝ) :
    core A D j rho t (hiPoint {i,l}) =
      1+rho*((D ∩ {i,l}).card:ℝ)-2*slopeBval t A j := by
  classical
  have hiA := others_not_mem_A A j i hi
  have hlA := others_not_mem_A A j l hl
  have hij := others_ne_j A j i hi
  have hlj := others_ne_j A j l hl
  have hAB : A ∩ {i,l} = ∅ := by ext x; simp; aesop
  have hBB : others A j ∩ {i,l} = {i,l} := by ext x; simp; aesop
  have hc : count (others A j) (hiPoint {i,l}) = 2 := by
    rw [count_hiPoint, hBB]; simp [hil]
  have hjf : hiPoint {i,l} j = false := by simp [hiPoint, Ne.symm hij, Ne.symm hlj]
  have hg : gate A j (hiPoint {i,l}) = 1 := by simp [gate, hjf, hc]
  rw [core_counts t A D j hjA hjD rho, hg, hjf, bit_false, mul_zero, add_zero,
    count_hiPoint, count_hiPoint, hAB, Finset.card_empty, Nat.cast_zero, mul_zero,
    sub_zero, hc]
  norm_num
  ring

theorem exists_B_pair (A : Finset (I n)) (j : I n) (hB2 : 2 ≤ (others A j).card) :
    ∃ i ∈ others A j, ∃ l ∈ others A j, i ≠ l := by
  obtain ⟨i, hi⟩ : (others A j).Nonempty := Finset.card_pos.mp (by omega)
  have he : 0 < ((others A j).erase i).card := by
    rw [Finset.card_erase_of_mem hi]; omega
  obtain ⟨l, hl⟩ := Finset.card_pos.mp he
  exact ⟨i, hi, l, Finset.mem_of_mem_erase hl, Ne.symm (Finset.ne_of_mem_erase hl)⟩

/-- Exact empty-D correction; no gate-firing assumption is imposed on D. -/
theorem maximum_empty (t : ℝ) (A : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (hB2 : 2 ≤ (others A j).card) (rho : ℝ)
    (ha : 0 ≤ gateMass t A j) (ha1 : gateMass t A j ≤ 1)
    (hb : 0 ≤ slopeBval t A j) :
    maxVal (core A ∅ j rho t) = 1-min (gateMass t A j) (2*slopeBval t A j) := by
  classical
  have hmA := min_le_left (gateMass t A j) (2*slopeBval t A j)
  have hmB := min_le_right (gateMass t A j) (2*slopeBval t A j)
  apply le_antisymm
  · apply maxVal_le
    intro x
    rw [core_counts t A ∅ j hjA (by simp) rho]
    simp only [count, Finset.filter_empty, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero]
    change gate A j x+(1-gateMass t A j)*bit (x j)
      -gateMass t A j*(count A x:ℝ)-slopeBval t A j*(count (others A j) x:ℝ) ≤ _
    have hna : 0 ≤ gateMass t A j*(count A x:ℝ) := mul_nonneg ha (Nat.cast_nonneg _)
    have hnb : 0 ≤ slopeBval t A j*(count (others A j) x:ℝ) := mul_nonneg hb (Nat.cast_nonneg _)
    cases hxj : x j
    · rw [bit_false, mul_zero, add_zero]
      by_cases hP : (∃ i ∈ A, x i = true) ∨ 2 ≤ count (others A j) x
      · have hg : gate A j x = 1 := by simp [gate, hxj, hP]
        rw [hg]
        rcases hP with hA | hB
        · have hc : (1:ℝ) ≤ count A x := by exact_mod_cast count_ge_one A x hA
          nlinarith
        · have hc : (2:ℝ) ≤ count (others A j) x := by exact_mod_cast hB
          nlinarith
      · have hg : gate A j x = 0 := by simp [gate, hxj, hP]
        rw [hg]; nlinarith
    · have hg : gate A j x = 0 := by simp [gate, hxj]
      rw [hg, bit_true, mul_one]; nlinarith
  · have hj := le_maxVal (core A ∅ j rho t) (hiPoint {j})
    rw [core_at_j A ∅ j hjA (by simp) rho t] at hj
    obtain ⟨i, hi, l, hl, hil⟩ := exists_B_pair A j hB2
    have hp := le_maxVal (core A ∅ j rho t) (hiPoint {i,l})
    rw [core_at_B_pair t A ∅ j i l hjA (by simp) hi hl hil rho] at hp
    simp only [Finset.empty_inter, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hp
    rcases le_total (gateMass t A j) (2*slopeBval t A j) with h | h
    · rw [min_eq_left h]; exact hj
    · rw [min_eq_right h]; exact hp

/-- Exact singleton-B correction; it costs one additional B coordinate to fire. -/
theorem maximum_singleton_B (t : ℝ) (A : Finset (I n)) (j i : I n)
    (hjA : j ∉ A) (hi : i ∈ others A j) (hB2 : 2 ≤ (others A j).card) (rho : ℝ)
    (ha : 0 ≤ gateMass t A j) (ha1 : gateMass t A j ≤ 1)
    (hb : 0 ≤ slopeBval t A j) (hba : slopeBval t A j ≤ gateMass t A j)
    (hbr : slopeBval t A j ≤ rho) :
    maxVal (core A {i} j rho t) = 1+rho-2*slopeBval t A j := by
  classical
  have hij := others_ne_j A j i hi
  have hjD : j ∉ ({i}:Finset (I n)) := by simpa using Ne.symm hij
  apply le_antisymm
  · apply maxVal_le
    intro x
    have hci : (count ({i}:Finset (I n)) x:ℝ) = bit (x i) := by
      rw [← sum_bits]; simp
    rw [core_counts t A {i} j hjA hjD rho, hci]
    have hbi := bit_bounds (x i)
    have hcnt := bit_le_count (others A j) i hi x
    have hna : 0 ≤ gateMass t A j*(count A x:ℝ) := mul_nonneg ha (Nat.cast_nonneg _)
    have hnb : slopeBval t A j*bit (x i) ≤ slopeBval t A j*(count (others A j) x:ℝ) :=
      mul_le_mul_of_nonneg_left hcnt hb
    have hlin : (rho-slopeBval t A j)*bit (x i) ≤ rho-slopeBval t A j := by
      nlinarith [hbi.2]
    cases hxj : x j
    · rw [bit_false, mul_zero, add_zero]
      by_cases hP : (∃ l ∈ A, x l = true) ∨ 2 ≤ count (others A j) x
      · have hg : gate A j x = 1 := by simp [gate, hxj, hP]
        rw [hg]
        rcases hP with hA | hB
        · have hc : (1:ℝ) ≤ count A x := by exact_mod_cast count_ge_one A x hA
          nlinarith
        · have hc : (2:ℝ) ≤ count (others A j) x := by exact_mod_cast hB
          have hgap : slopeBval t A j*(1+bit (x i)) ≤ slopeBval t A j*(count (others A j) x:ℝ) := by
            apply mul_le_mul_of_nonneg_left _ hb
            linarith [hbi.2]
          nlinarith
      · have hg : gate A j x = 0 := by simp [gate, hxj, hP]
        rw [hg]; nlinarith
    · have hg : gate A j x = 0 := by simp [gate, hxj]
      rw [hg, bit_true, mul_one]; nlinarith
  · have he : 0 < ((others A j).erase i).card := by rw [Finset.card_erase_of_mem hi]; omega
    obtain ⟨l, hl⟩ := Finset.card_pos.mp he
    have hli := Finset.ne_of_mem_erase hl
    have hp := le_maxVal (core A {i} j rho t) (hiPoint {i,l})
    rw [core_at_B_pair t A {i} j i l hjA hjD hi (Finset.mem_of_mem_erase hl) (Ne.symm hli) rho] at hp
    have hint : ({i}:Finset (I n)) ∩ {i,l} = {i} := by ext x; simp; tauto
    simpa [hint] using hp

#print axioms sum_bits
#print axioms core_counts
#print axioms core_at_B_pair
#print axioms maximum_empty
#print axioms maximum_singleton_B
end
end CIGAMF.P13.D6ReferenceMaximumBranches
