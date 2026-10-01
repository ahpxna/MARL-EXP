import «LeanD6ReferenceMinimumBranchesV1»
import «LeanD6ReferenceMaximumBranchesV1»
import «LeanD6ReferenceCenteredGeometryV1»

/-! D04: actual retained loss at every Bernoulli reference t in [0,1],
rho >= 1, including empty/singleton-B maxima and both minimum branches.
No hfire, hA, or (k-2)b>=1 restriction. This does not prove symmetry averaging
or minimax over hidden worlds; it proves exact reduction of decision loss. -/
namespace CIGAMF.P13.D6ReferenceFullCountLoss
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge CIGAMF.P13.D6ReferenceTail
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.P13.D6ReferenceRetainedOscillation
open CIGAMF.P13.D6ReferenceMinimumBranches CIGAMF.P13.D6ReferenceMaximumBranches
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference CIGAMF.V4.SupportGeometry
noncomputable section
variable {n : ℕ}

theorem slope_gap (t : ℝ) (A : Finset (I n)) (j : I n)
    (hB2 : 2 ≤ (others A j).card) :
    gateMass t A j-slopeBval t A j = (1-t)^(A.card+(others A j).card-1) := by
  obtain ⟨m, hm⟩ : ∃ m, (others A j).card = m+2 := ⟨(others A j).card-2, by omega⟩
  unfold gateMass tailFactor slopeBval
  rw [hm]
  simp only [show m+2-1=m+1 by omega,
    show A.card+(m+2)-1=A.card+m+1 by omega, pow_succ, pow_add]
  push_cast
  ring

theorem slope_order (t : ℝ) (ht1 : t ≤ 1) (A : Finset (I n)) (j : I n)
    (hB2 : 2 ≤ (others A j).card) : slopeBval t A j ≤ gateMass t A j := by
  have h := slope_gap t A j hB2
  have hp : 0 ≤ (1-t)^(A.card+(others A j).card-1) := pow_nonneg (by linarith) _
  linarith

def upperCount (a b rho : ℝ) (u v : ℕ) : ℝ :=
  1+(rho-a)*(u:ℝ)+(rho-b)*(v:ℝ)
    -(if u=0 ∧ v=0 then min a (2*b) else if u=0 ∧ v=1 then b else 0)

def countLoss (a b rho : ℝ) (na nb u v : ℕ) : ℝ :=
  (upperCount a b rho u v
    -min ((1-a)-a*((na:ℝ)-(u:ℝ))-b*((nb:ℝ)-(v:ℝ)))
      (if v < nb then -b else 0))/2

theorem fire_iff_counts (A D : Finset (I n)) (j : I n) :
    ((∃ i ∈ A, i ∈ D) ∨ 2 ≤ (D ∩ others A j).card) ↔
      (0 < (D ∩ A).card ∨ 2 ≤ (D ∩ others A j).card) := by
  have h : (∃ i ∈ A, i ∈ D) ↔ 0 < (D ∩ A).card := by
    rw [Finset.card_pos]
    constructor
    · rintro ⟨i, hiA, hiD⟩; exact ⟨i, Finset.mem_inter.mpr ⟨hiD, hiA⟩⟩
    · rintro ⟨i, hi⟩; exact ⟨i, (Finset.mem_inter.mp hi).2, (Finset.mem_inter.mp hi).1⟩
  rw [h]

theorem nonfire_classification (A D : Finset (I n)) (j : I n) (hjD : j ∉ D)
    (h : ¬ ((∃ i ∈ A, i ∈ D) ∨ 2 ≤ (D ∩ others A j).card)) :
    D = ∅ ∨ ∃ i ∈ others A j, D = {i} := by
  classical
  have hDB : D ⊆ others A j := by
    intro i hi
    apply (mem_others_iff A j i).mpr
    exact ⟨by rintro rfl; exact hjD hi, fun hiA => h (Or.inl ⟨i, hiA, hi⟩)⟩
  have hc : D.card ≤ 1 := by
    have he : D ∩ others A j = D := Finset.inter_eq_left.mpr hDB
    have hno : ¬ 2 ≤ (D ∩ others A j).card := fun h2 => h (Or.inr h2)
    rw [he] at hno
    omega
  by_cases he : D = ∅
  · exact Or.inl he
  · have hpos : 0 < D.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (by omega : D.card=1)
    right
    refine ⟨i, hDB ?_, hi⟩
    rw [hi]; simp

theorem maximum_exact (t : ℝ) (A D : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (hjD : j ∉ D) (hB2 : 2 ≤ (others A j).card) (rho : ℝ)
    (ha : 0 ≤ gateMass t A j) (ha1 : gateMass t A j ≤ 1)
    (hb : 0 ≤ slopeBval t A j) (hba : slopeBval t A j ≤ gateMass t A j)
    (har : gateMass t A j ≤ rho) :
    maxVal (core A D j rho t) = upperCount (gateMass t A j) (slopeBval t A j) rho
      (D ∩ A).card (D ∩ others A j).card := by
  classical
  have hbr := le_trans hba har
  by_cases hf : (∃ i ∈ A, i ∈ D) ∨ 2 ≤ (D ∩ others A j).card
  · have hc := (fire_iff_counts A D j).mp hf
    have hn0 : ¬ ((D ∩ A).card=0 ∧ (D ∩ others A j).card=0) := by omega
    have hn1 : ¬ ((D ∩ A).card=0 ∧ (D ∩ others A j).card=1) := by omega
    have hm : maxVal (core A D j rho t) =
        1+((rho-gateMass t A j)*((D ∩ A).card:ℝ)
          +(rho-slopeBval t A j)*((D ∩ others A j).card:ℝ)) := by
      apply le_antisymm
      · exact maxVal_le _ (core_le t A D j hjD rho ha hb har hbr)
      · have h := le_maxVal (core A D j rho t) (hiPoint D)
        rw [hi_value t A D j hjD rho hf] at h
        exact h
    rw [hm]
    simp only [upperCount, if_neg hn0, if_neg hn1, sub_zero]
    ring
  · rcases nonfire_classification A D j hjD hf with hE | ⟨i, hi, hI⟩
    · subst D
      rw [maximum_empty t A j hjA hB2 rho ha ha1 hb]
      simp [upperCount]
    · subst D
      rw [maximum_singleton_B t A j i hjA hi hB2 rho ha ha1 hb hba hbr]
      have hiA := others_not_mem_A A j i hi
      have h1 : ({i}:Finset (I n)) ∩ A = ∅ := by ext x; simp; aesop
      have h2 : ({i}:Finset (I n)) ∩ others A j = {i} := by ext x; simp; aesop
      simp [upperCount, h1, h2]
      ring

theorem offValue_counts (A D : Finset (I n)) (j : I n) (t : ℝ) :
    offValue A D j t =
      if (D ∩ others A j).card < (others A j).card then -slopeBval t A j else 0 := by
  classical
  have hnat : (D ∩ others A j).card+(Dᶜ ∩ others A j).card=(others A j).card := by
    exact_mod_cast card_compl_split (others A j) D
  have hiff : (Dᶜ ∩ others A j).Nonempty ↔ (D ∩ others A j).card < (others A j).card := by
    rw [← Finset.card_pos]; omega
  simp only [offValue, hiff]

theorem lowValue_counts (A D : Finset (I n)) (j : I n) (t : ℝ) :
    lowValue A D j t = (1-gateMass t A j)
      -gateMass t A j*((A.card:ℝ)-((D ∩ A).card:ℝ))
      -slopeBval t A j*(((others A j).card:ℝ)-((D ∩ others A j).card:ℝ)) := by
  have hA := card_compl_split A D
  have hB := card_compl_split (others A j) D
  unfold lowValue
  rw [← hA, ← hB]
  ring

/-- Full actual loss law. No unproved distribution or geometry assumptions. -/
theorem actual_full_count_loss (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (A T S : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjT : j ∉ T)
    (hB2 : 2 ≤ (others A j).card) (rho : ℝ) (hr : 1 ≤ rho) :
    productCompressionLoss (centeredWorld A T j rho t)
        (productResponse (bern t) (centeredWorld A T j rho t)) S
      = countLoss (gateMass t A j) (slopeBval t A j) rho A.card (others A j).card
          ((T \ S) ∩ A).card ((T \ S) ∩ others A j).card := by
  have hjD : j ∉ T \ S := fun h => hjT (Finset.mem_sdiff.mp h).1
  have ha := gateMass_bounds t ht0 ht1 A j (by omega : 1 ≤ (others A j).card)
  have hb := slopeBval_nonneg t ht0 ht1 A j hB2
  have hba := slope_order t ht1 A j hB2
  have har := le_trans ha.2 hr
  rw [retained_loss t A T S j hjA hB2 rho, osc,
    maximum_exact t A (T \ S) j hjA hjD hB2 rho ha.1 ha.2 hb hba har,
    minimum_exact t A (T \ S) j hjA hjD rho ha.1 hb har (le_trans hba har),
    lowValue_counts, offValue_counts]
  rfl

theorem same_counts_same_loss (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (A T S₁ S₂ : Finset (I n)) (j : I n) (hjA : j ∉ A) (hjT : j ∉ T)
    (hB2 : 2 ≤ (others A j).card) (rho : ℝ) (hr : 1 ≤ rho)
    (hA : ((T \ S₁) ∩ A).card = ((T \ S₂) ∩ A).card)
    (hB : ((T \ S₁) ∩ others A j).card = ((T \ S₂) ∩ others A j).card) :
    productCompressionLoss (centeredWorld A T j rho t)
        (productResponse (bern t) (centeredWorld A T j rho t)) S₁
      = productCompressionLoss (centeredWorld A T j rho t)
        (productResponse (bern t) (centeredWorld A T j rho t)) S₂ := by
  rw [actual_full_count_loss t ht0 ht1 A T S₁ j hjA hjT hB2 rho hr,
    actual_full_count_loss t ht0 ht1 A T S₂ j hjA hjT hB2 rho hr, hA, hB]

#print axioms slope_gap
#print axioms slope_order
#print axioms nonfire_classification
#print axioms maximum_exact
#print axioms offValue_counts
#print axioms lowValue_counts
#print axioms actual_full_count_loss
#print axioms same_counts_same_loss
end
end CIGAMF.P13.D6ReferenceFullCountLoss
