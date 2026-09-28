import «LeanD6AllocationSharpV1»

/-! Push the explicit indexed primal allocation onto the actual finite
measurement library. Repeated query indices are aggregated, so normalization
and the information identity do not silently assume query injectivity. -/
namespace CIGAMF.P13.D6AllocationDistribution
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationPrimalBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6ExpandedAllocation
open CIGAMF.P13.D6AllocationSharp
noncomputable section
variable {n : ℕ}

def primalQueries (A : Finset (I n)) (j : I n) : Finset (Measurement n) :=
  insert (.inr (others A j,true)) (A.image fun a => .inr (A.erase a,false))

def primalWeight (A : Finset (I n)) (j : I n) (q : ℝ) (e : Measurement n) : ℝ :=
  (if e = .inr (others A j,true) then weight q (scale q) else 0) +
    ∑ a ∈ A, if e = .inr (A.erase a,false) then (1-weight q (scale q))/(q+1) else 0

/-- Finite pushforward identity, for any observable on actual measurements. -/
theorem primal_sum (A : Finset (I n)) (j : I n) (q : ℝ) (f : Measurement n → ℝ) :
    (∑ e ∈ primalQueries A j, primalWeight A j q e*f e) =
      ((1-weight q (scale q))/(q+1))*(∑ a ∈ A, f (.inr (A.erase a,false))) +
        weight q (scale q)*f (.inr (others A j,true)) := by
  have hb : (.inr (others A j,true) : Measurement n) ∈ primalQueries A j := by
    simp [primalQueries]
  have ha : ∀ a ∈ A, (.inr (A.erase a,false) : Measurement n) ∈ primalQueries A j := by
    intro a ha
    exact mem_insert_of_mem (mem_image_of_mem _ ha)
  unfold primalWeight
  simp only [add_mul, sum_add_distrib, sum_mul]
  have hbSum : (∑ e ∈ primalQueries A j,
      (if e = .inr (others A j,true) then weight q (scale q) else 0)*f e) =
        weight q (scale q)*f (.inr (others A j,true)) := by
    simp [ite_mul, hb]
  rw [hbSum, sum_comm]
  have haSum : (∑ a ∈ A, ∑ e ∈ primalQueries A j,
      (if e = .inr (A.erase a,false) then (1-weight q (scale q))/(q+1) else 0)*f e) =
        ((1-weight q (scale q))/(q+1))*(∑ a ∈ A, f (.inr (A.erase a,false))) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a hmem
    simp [ite_mul, ha a hmem]
  rw [haSum]
  ring

/-- This is a legal normalized distribution on `Measurement`, rather than
only a collection of indexed orbit weights. -/
theorem primal_distribution (A : Finset (I n)) (j : I n) (q : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    (∀ e ∈ primalQueries A j, Legal j q e) ∧
    (∀ e : Measurement n, 0 ≤ primalWeight A j q e) ∧
    (∑ e ∈ primalQueries A j, primalWeight A j q e)=1 := by
  have hp := primal_feasible A j q hq hj hA hB
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases mem_insert.mp he with he | he
    · subst e
      exact hp.2.2.2.1
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp he
      exact hp.2.2.2.2 a ha
  · intro e
    unfold primalWeight
    apply add_nonneg
    · split <;> first | exact hp.1 | exact le_refl 0
    · apply sum_nonneg
      intro a ha
      split <;> first | exact hp.2.1 | exact le_refl 0
  · have he := primal_sum A j q (fun _ => 1)
    simp only [mul_one, sum_const, nsmul_eq_mul] at he
    have hn := hp.2.2.1
    simp only [sum_const, nsmul_eq_mul] at hn
    nlinarith [he]

/-- The weighted game expression on actual measurements is exactly the
primal already connected to the D6 world evaluations. -/
theorem primal_information_eq (A A' : Finset (I n)) (j : I n) (q nu : ℝ) :
    (∑ e ∈ primalQueries A j, primalWeight A j q e*information A A' j (1/2) nu e) =
      actualPrimal A A' j q (scale q) (2*(1-nu)) := by
  rw [primal_sum]
  unfold actualPrimal
  have ht : 1-2*(1-nu)/2=nu := by ring
  rw [ht]
  rfl

/-- One feasible distribution guarantees the sharp value simultaneously
against every distinct legal D6 hidden set and every nuisance margin. -/
theorem primal_distribution_lower (A A' : Finset (I n)) (j : I n) (q nu : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hj' : j ∉ A') (hcard : A'.card=A.card) (hne : A' ≠ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    value q (scale q)/8 ≤
      ∑ e ∈ primalQueries A j, primalWeight A j q e*information A A' j (1/2) nu e := by
  rw [primal_information_eq]
  exact every_alternative_primal_lower A A' j q nu hq hj hj' hcard hne hA hB

/-- The actual primal has an admissible worst alternative attaining equality.
The hidden alternative is outside the sum over all measurements. -/
theorem primal_attains_information_value (A : Finset (I n)) (j : I n) (q : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    ∃ A' : Finset (I n), ∃ nu : ℝ,
      A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧ 0 ≤ nu ∧ nu ≤ 1 ∧
      (∑ e ∈ primalQueries A j, primalWeight A j q e*information A A' j (1/2) nu e) =
        value q (scale q)/8 := by
  have hp := primal_distribution A j q hq hj hA hB
  obtain ⟨A',nu,hne,hcard,hj',hnu,hnu1,hu⟩ :=
    arbitrary_allocation_upper A j q hq hj hA hB (primalQueries A j) (primalWeight A j q)
      hp.1 (fun e _ => hp.2.1 e) hp.2.2
  exact ⟨A',nu,hne,hcard,hj',hnu,hnu1,
    le_antisymm hu (primal_distribution_lower A A' j q nu hq hj hj' hcard hne hA hB)⟩

/-- Both sides now use the same finite-measurement allocation game: an
explicit feasible allocation attains the rate, and every feasible allocation
has one admissible alternative with information at most that rate. -/
theorem sharp_finite_allocation_game (A : Finset (I n)) (j : I n) (q : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    (∃ (E : Finset (Measurement n)) (w : Measurement n → ℝ),
      (∀ e ∈ E, Legal j q e) ∧ (∀ e ∈ E, 0 ≤ w e) ∧ (∑ e ∈ E, w e)=1 ∧
      (∀ A' : Finset (I n), j ∉ A' → A'.card=A.card → A' ≠ A → ∀ nu : ℝ,
        0 ≤ nu → nu ≤ 1 → value q (scale q)/8 ≤
          ∑ e ∈ E, w e*information A A' j (1/2) nu e)) ∧
    (∀ (E : Finset (Measurement n)) (w : Measurement n → ℝ),
      (∀ e ∈ E, Legal j q e) → (∀ e ∈ E, 0 ≤ w e) → (∑ e ∈ E, w e)=1 →
      ∃ A' : Finset (I n), ∃ nu : ℝ,
        A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧ 0 ≤ nu ∧ nu ≤ 1 ∧
        (∑ e ∈ E, w e*information A A' j (1/2) nu e) ≤ value q (scale q)/8) := by
  have hp := primal_distribution A j q hq hj hA hB
  constructor
  · refine ⟨primalQueries A j, primalWeight A j q, hp.1, (fun e _ => hp.2.1 e), hp.2.2, ?_⟩
    intro A' hj' hcard hne nu _ _
    exact primal_distribution_lower A A' j q nu hq hj hj' hcard hne hA hB
  · intro E w hl hw hn
    exact arbitrary_allocation_upper A j q hq hj hA hB E w hl hw hn

#print axioms primal_sum
#print axioms primal_distribution
#print axioms primal_information_eq
#print axioms primal_distribution_lower
#print axioms primal_attains_information_value
#print axioms sharp_finite_allocation_game
end
end CIGAMF.P13.D6AllocationDistribution
