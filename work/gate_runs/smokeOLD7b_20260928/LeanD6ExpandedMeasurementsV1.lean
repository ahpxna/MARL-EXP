import «LeanD6ThresholdConstructionV1»

/-! Actual-world semantics for joint measurements without the distinguished
coordinate. This closes the observation bridge used by the expanded-query
allocation experiments. It does not claim the allocation game's finite-orbit
reduction or sequential optimality. -/
namespace CIGAMF.P13.D6ExpandedMeasurements
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold
variable {n : ℕ}

def plainCorner (G : Finset (I n)) : I n → Bool := fun i => decide (i ∈ G)

theorem count_plain (B G : Finset (I n)) : count B (plainCorner G) = (G ∩ B).card := by
  unfold count
  congr 1
  ext i
  simp [plainCorner, and_comm]

/-- Every unanchored query of size at least two has gate value one, for every
hidden A. Thus this query model is derived from the threshold construction. -/
theorem gate_plain (A G : Finset (I n)) (j : I n) (hjG : j ∉ G) (hG : 2 ≤ G.card) :
    gate A j (plainCorner G) = 1 := by
  have he : (∃ i ∈ A, plainCorner G i = true) ∨ 2 ≤ count (others A j) (plainCorner G) := by
    by_cases h : ∃ i ∈ A, plainCorner G i = true
    · exact Or.inl h
    · right
      have hs : G ⊆ others A j := by
        intro i hi
        have hiA : i ∉ A := by
          intro hiA
          exact h ⟨i, hiA, by simp [plainCorner, hi]⟩
        have hij : i ≠ j := by intro hh; subst i; exact hjG hi
        simp [others, hiA, hij]
      rw [count_plain, inter_eq_left.mpr hs]
      exact hG
  have hjfalse : plainCorner G j = false := by simp [plainCorner, hjG]
  simp only [gate, hjfalse, Bool.false_eq_true, ↓reduceIte, if_pos he]

/-- Actual unanchored response: one plus lambda times the queried B count. -/
theorem actual_unanchored_measurement (A G : Finset (I n)) (j : I n)
    (hjG : j ∉ G) (hG : 2 ≤ G.card) (mu : ℝ) :
    world A j mu (plainCorner G) = 1+(1-mu)*((G ∩ others A j).card : ℝ) := by
  have hw : ∀ i, coeff A j mu i * bit (plainCorner G i) =
      if i ∈ G ∩ others A j then 1-mu else 0 := by
    intro i
    by_cases hij : i = j
    · subst i
      simp [plainCorner, bit, hjG, others]
    · by_cases hiA : i ∈ A <;> by_cases hiG : i ∈ G <;>
        simp [coeff, plainCorner, bit, others, hiA, hiG, hij]
  rw [world, gate_plain A G j hjG hG]
  unfold linear
  simp_rw [hw]
  simp only [Finset.sum_ite_mem, univ_inter, sum_const]
  simp
  ring

/-- The two query types differ by the same unknown lambda plus a known one.
Paired responses therefore identify the nuisance independently of hidden A. -/
theorem paired_measurement_calibrates_margin (A G : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (hjG : j ∉ G) (hG : 2 ≤ G.card) (mu : ℝ) :
    world A j mu (plainCorner G) - world A j mu (jointCorner G j) = 2-mu := by
  rw [actual_unanchored_measurement A G j hjG hG, joint_measurement A G j hjA]
  ring

#print axioms gate_plain
#print axioms actual_unanchored_measurement
#print axioms paired_measurement_calibrates_margin
end CIGAMF.P13.D6ExpandedMeasurements
