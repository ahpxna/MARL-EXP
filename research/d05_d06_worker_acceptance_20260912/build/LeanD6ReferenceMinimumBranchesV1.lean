import «LeanD6ReferenceRetainedOscillationV1»

/-! # D04: exact minimum on both gate branches.

The earlier sign-region formula assumed that the complement corner minimizes
`core`. Here the competing gate-off corner is included. All statements are on
the actual Boolean cube. No `hA` sign-region assumption remains. The maximum
formula below still requires the separately stated gate-firing condition.
-/
namespace CIGAMF.P13.D6ReferenceMinimumBranches
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge CIGAMF.P13.D6ReferenceTail
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.P13.D6ReferenceRetainedOscillation
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference CIGAMF.V4.SupportGeometry
noncomputable section
variable {n : ℕ}

theorem core_ge_active (t : ℝ) (A D : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjD : j ∉ D)
    (rho : ℝ) (hG0 : 0 ≤ gateMass t A j) (hs0 : 0 ≤ slopeBval t A j)
    (hGr : gateMass t A j ≤ rho) (hsr : slopeBval t A j ≤ rho)
    (x : I n → Bool)
    (hactive : x j = true ∨ (∃ i ∈ A, x i = true) ∨ 2 ≤ count (others A j) x) :
    (1-gateMass t A j)-gateMass t A j*((Dᶜ ∩ A).card:ℝ)
        -slopeBval t A j*((Dᶜ ∩ others A j).card:ℝ)
      ≤ core A D j rho t x := by
  classical
  have hjU : j ∈ (Finset.univ : Finset (I n)) := Finset.mem_univ j
  have hsplit : linear (retainedCoeff A D j rho t) x
      = retainedCoeff A D j rho t j*bit (x j)
        +∑ i ∈ (Finset.univ : Finset (I n)).erase j,
            retainedCoeff A D j rho t i*bit (x i) := by
    unfold linear
    rw [← Finset.add_sum_erase (Finset.univ : Finset (I n))
      (fun i => retainedCoeff A D j rho t i*bit (x i)) hjU]
  have hrj : retainedCoeff A D j rho t j = 1-gateMass t A j := by
    unfold retainedCoeff
    rw [if_neg hjD, gateSlope_at_j]
    ring
  have hsign : ∀ i, i ≠ j → i ∈ D → 0 ≤ retainedCoeff A D j rho t i := by
    intro i hij hiD
    unfold retainedCoeff
    rw [if_pos hiD]
    by_cases hiA : i ∈ A
    · rw [gateSlope_mem_A t A j i hij hiA]; linarith
    · rw [gateSlope_others t A j i hij hiA]; linarith
  have hsign' : ∀ i, i ≠ j → i ∉ D → retainedCoeff A D j rho t i ≤ 0 := by
    intro i hij hiD
    unfold retainedCoeff
    rw [if_neg hiD]
    by_cases hiA : i ∈ A
    · rw [gateSlope_mem_A t A j i hij hiA]; linarith
    · rw [gateSlope_others t A j i hij hiA]; linarith
  -- the full tail bound, valid whenever the `j` coordinate carries `1 - gateMass`
  have hfullEq : ((Finset.univ : Finset (I n)).erase j) ∩ Dᶜ = Dᶜ.erase j := by
    ext i
    constructor
    · intro h
      have h1 := Finset.mem_erase.mp (Finset.mem_inter.mp h).1
      exact Finset.mem_erase.mpr ⟨h1.1, (Finset.mem_inter.mp h).2⟩
    · intro h
      have h1 := Finset.mem_erase.mp h
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_erase.mpr ⟨h1.1, Finset.mem_univ i⟩, h1.2⟩
  have hfull : (∑ i ∈ Dᶜ.erase j, retainedCoeff A D j rho t i)
      ≤ ∑ i ∈ (Finset.univ : Finset (I n)).erase j,
          retainedCoeff A D j rho t i*bit (x i) := by
    have hb : ∀ i ∈ (Finset.univ : Finset (I n)).erase j,
        (if i ∈ Dᶜ then retainedCoeff A D j rho t i else 0)
          ≤ retainedCoeff A D j rho t i*bit (x i) := by
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      have hbb := bit_bounds (x i)
      by_cases hiD : i ∈ D
      · rw [if_neg (by simpa using hiD)]
        nlinarith [hsign i hij hiD, hbb.1]
      · rw [if_pos (by simpa using hiD)]
        nlinarith [hsign' i hij hiD, hbb.2]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hb)
    rw [Finset.sum_ite_mem, hfullEq]
  have htailval := lo_tail_sum t A D j hjA rho
  cases hxj : x j with
  | true =>
      have hg : gate A j x = 0 := by simp [gate, hxj]
      unfold core
      rw [hsplit, hg, hrj, hxj, bit_true, mul_one]
      linarith [hfull, htailval]
  | false =>
      have hP : (∃ i ∈ A, x i = true) ∨ 2 ≤ count (others A j) x := by
        rcases hactive with h | h
        · simp [hxj] at h
        · exact h
      have hg : gate A j x = 1 := by simp [gate, hxj, hP]
      unfold core
      rw [hsplit, hg, hrj, hxj, bit_false, mul_zero, zero_add]
      linarith [hfull, htailval]

/-- A gate-off point has either no active coordinate, or exactly one in B. -/
theorem gate_off_point (A : Finset (I n)) (j : I n) (x : I n → Bool)
    (hj : x j = false)
    (hP : ¬ ((∃ i ∈ A, x i = true) ∨ 2 ≤ count (others A j) x)) :
    x = hiPoint ∅ ∨ ∃ i ∈ others A j, x = hiPoint {i} := by
  classical
  have hAoff : ∀ i ∈ A, x i = false := by
    intro i hi
    cases hx : x i with
    | false => rfl
    | true => exact False.elim (hP (Or.inl ⟨i, hi, hx⟩))
  have hone : ((others A j).filter (fun i => x i = true)).card ≤ 1 := by
    have h : ¬ 2 ≤ count (others A j) x := fun h => hP (Or.inr h)
    unfold count at h
    omega
  by_cases hsome : ∃ i ∈ others A j, x i = true
  · obtain ⟨i, hi, hxi⟩ := hsome
    right
    refine ⟨i, hi, ?_⟩
    funext l
    by_cases hli : l = i
    · subst l
      simp [hiPoint, hxi]
    · have hxlf : x l = false := by
        cases hl : x l with
        | false => rfl
        | true =>
            have hlj : l ≠ j := by rintro rfl; simp [hj] at hl
            have hlA : l ∉ A := by intro hm; have := hAoff l hm; simp [hl] at this
            have hlB := (mem_others_iff A j l).mpr ⟨hlj, hlA⟩
            have he := Finset.card_le_one.mp hone l (by simp [hlB, hl])
              i (by simp [hi, hxi])
            exact False.elim (hli he)
      simp [hiPoint, hli, hxlf]
  · left
    funext l
    have hxf : x l = false := by
      cases hl : x l with
      | false => rfl
      | true =>
          have hlj : l ≠ j := by rintro rfl; simp [hj] at hl
          have hlA : l ∉ A := by intro hm; have := hAoff l hm; simp [hl] at this
          exact False.elim (hsome ⟨l, (mem_others_iff A j l).mpr ⟨hlj, hlA⟩, hl⟩)
    simp [hiPoint, hxf]

theorem core_zero (A D : Finset (I n)) (j : I n) (rho t : ℝ) :
    core A D j rho t (hiPoint ∅) = 0 := by
  simp [core, gate, linear, count, hiPoint, bit]

theorem core_singleton_B (A D : Finset (I n)) (j i : I n)
    (hi : i ∈ others A j) (rho t : ℝ) :
    core A D j rho t (hiPoint {i}) = (if i ∈ D then rho else 0)-slopeBval t A j := by
  classical
  have hij := others_ne_j A j i hi
  have hiA := others_not_mem_A A j i hi
  have hf : (others A j).filter (fun l => hiPoint {i} l = true) = {i} := by
    ext l
    simp only [Finset.mem_filter, hiPoint, decide_eq_true_eq, Finset.mem_singleton]
    constructor
    · exact And.right
    · intro h; subst l; exact ⟨hi, rfl⟩
  have hg : gate A j (hiPoint {i}) = 0 := by
    have hno : ¬ ∃ l ∈ A, hiPoint {i} l = true := by
      rintro ⟨l, hl, hli⟩
      have : l = i := by simpa [hiPoint] using hli
      subst l
      exact hiA hl
    have hjf : hiPoint {i} j = false := by simp [hiPoint, Ne.symm hij]
    have hc : count (others A j) (hiPoint {i}) = 1 := by
      unfold count
      rw [hf]
      simp
    simp [gate, hjf, hno, hc]
  have hl : linear (retainedCoeff A D j rho t) (hiPoint {i})
      = retainedCoeff A D j rho t i := by
    unfold linear
    rw [Finset.sum_eq_single i]
    · simp [hiPoint, bit]
    · intro l _ hli; simp [hiPoint, hli, bit]
    · simp
  rw [core, hg, hl, zero_add]
  unfold retainedCoeff
  rw [gateSlope_others t A j i hij hiA]

def lowValue (A D : Finset (I n)) (j : I n) (t : ℝ) : ℝ :=
  (1-gateMass t A j)-gateMass t A j*((Dᶜ ∩ A).card:ℝ)
    -slopeBval t A j*((Dᶜ ∩ others A j).card:ℝ)

def offValue (A D : Finset (I n)) (j : I n) (t : ℝ) : ℝ :=
  if (Dᶜ ∩ others A j).Nonempty then -slopeBval t A j else 0

/-- The gate-off optimum is an attained value, even when no B coordinate is omitted. -/
theorem offValue_attained (A D : Finset (I n)) (j : I n) (rho t : ℝ) :
    ∃ x, core A D j rho t x = offValue A D j t := by
  classical
  by_cases h : (Dᶜ ∩ others A j).Nonempty
  · have hne := h
    obtain ⟨i, hi⟩ := h
    have hiD : i ∉ D := by simpa using (Finset.mem_inter.mp hi).1
    refine ⟨hiPoint {i}, ?_⟩
    rw [core_singleton_B A D j i (Finset.mem_inter.mp hi).2 rho t]
    simp [offValue, hne, hiD]
  · exact ⟨hiPoint ∅, by rw [core_zero]; simp [offValue, h]⟩

theorem offValue_le_zero (A D : Finset (I n)) (j : I n) (t : ℝ)
    (hb : 0 ≤ slopeBval t A j) : offValue A D j t ≤ 0 := by
  unfold offValue
  split_ifs <;> linarith

/-- Exact whole-cube minimum, with no sign-region restriction. -/
theorem minimum_exact (t : ℝ) (A D : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (hjD : j ∉ D) (rho : ℝ)
    (ha : 0 ≤ gateMass t A j) (hb : 0 ≤ slopeBval t A j)
    (har : gateMass t A j ≤ rho) (hbr : slopeBval t A j ≤ rho) :
    minVal (core A D j rho t) = min (lowValue A D j t) (offValue A D j t) := by
  classical
  apply le_antisymm
  · apply le_min
    · have h := minVal_le (core A D j rho t) (loPoint D)
      rw [lo_value t A D j hjA hjD rho] at h
      exact h
    · obtain ⟨x, hx⟩ := offValue_attained A D j rho t
      exact hx ▸ minVal_le (core A D j rho t) x
  · apply le_minVal
    intro x
    by_cases hactive : x j = true ∨ (∃ i ∈ A, x i = true) ∨ 2 ≤ count (others A j) x
    · exact le_trans (min_le_left _ _) (core_ge_active t A D j hjA hjD rho ha hb har hbr x hactive)
    · have hj : x j = false := by cases hx : x j <;> simp_all
      have hP : ¬ ((∃ i ∈ A, x i = true) ∨ 2 ≤ count (others A j) x) :=
        fun h => hactive (Or.inr h)
      apply le_trans (min_le_right _ _)
      rcases gate_off_point A j x hj hP with hzero | ⟨i, hi, hxi⟩
      · rw [hzero, core_zero]
        exact offValue_le_zero A D j t hb
      · rw [hxi, core_singleton_B A D j i hi rho t]
        by_cases hiD : i ∈ D
        · rw [if_pos hiD]
          exact le_trans (offValue_le_zero A D j t hb) (sub_nonneg.mpr hbr)
        · have hne : (Dᶜ ∩ others A j).Nonempty := ⟨i, by simp [hiD, hi]⟩
          simp [offValue, hne, hiD]

/-- Exact loss on the gate-firing maximum branch; minimum branch switching is included. -/
theorem retained_loss_two_minima (t : ℝ) (A T S : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (hjT : j ∉ T) (hB2 : 2 ≤ (others A j).card) (rho : ℝ)
    (ha : 0 ≤ gateMass t A j) (hb : 0 ≤ slopeBval t A j)
    (har : gateMass t A j ≤ rho) (hbr : slopeBval t A j ≤ rho)
    (hfire : (∃ i ∈ A, i ∈ T \ S) ∨ 2 ≤ ((T \ S) ∩ others A j).card) :
    productCompressionLoss (centeredWorld A T j rho t)
        (productResponse (bern t) (centeredWorld A T j rho t)) S
      = ((1+(rho-gateMass t A j)*(((T \ S) ∩ A).card:ℝ)
          +(rho-slopeBval t A j)*(((T \ S) ∩ others A j).card:ℝ))
          -min (lowValue A (T \ S) j t) (offValue A (T \ S) j t))/2 := by
  have hjD : j ∉ T \ S := fun h => hjT (Finset.mem_sdiff.mp h).1
  rw [retained_loss t A T S j hjA hB2 rho, osc,
    minimum_exact t A (T \ S) j hjA hjD rho ha hb har hbr]
  have hm : maxVal (core A (T \ S) j rho t) =
      1+((rho-gateMass t A j)*(((T \ S) ∩ A).card:ℝ)
        +(rho-slopeBval t A j)*(((T \ S) ∩ others A j).card:ℝ)) := by
    apply le_antisymm
    · exact maxVal_le _ (core_le t A (T \ S) j hjD rho ha hb har hbr)
    · have h := le_maxVal (core A (T \ S) j rho t) (hiPoint (T \ S))
      rw [hi_value t A (T \ S) j hjD rho hfire] at h
      exact h
  rw [hm]
  ring

#print axioms core_ge_active
#print axioms gate_off_point
#print axioms core_zero
#print axioms core_singleton_B
#print axioms offValue_attained
#print axioms minimum_exact
#print axioms retained_loss_two_minima
end
end CIGAMF.P13.D6ReferenceMinimumBranches
