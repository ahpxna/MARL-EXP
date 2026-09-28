import «LeanFunctionalRankingV6»

/-! F5: the actual finite group-range answer boundary is a union of polyhedra.

This uses FunctionalBoundary.capacity and FunctionalRanking.StrictTopK, not a
Top-1 surrogate. Extrema are chosen from the ALTERNATIVE, never frozen at truth.
The existing FunctionalFullOracle handles two Fin-3 relations with diagonal
energy. Here the boundary identity allows arbitrary finite action/relation sets
and an arbitrary energy functional, including coupled contrast measurements.

The statements use the closed/tie boundary. Strict rank inversion, a QP dual,
optimal allocation, setup-cost phases, and an adaptive algorithm are NOT proved.
Source written for worker compilation; no compilation is claimed in this handoff.
-/
namespace CIGAMF.P13.FunctionalRangeAlternativeUnion

open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V4.FunctionalBoundary
open CIGAMF.V6.FunctionalRanking

variable {A R : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
  [Fintype R] [DecidableEq R]

theorem pair_le_capacity (f : A → ℝ) (a b : A) :
    f a - f b ≤ capacity f := by
  have hmax := le_maxVal f a
  have hmin := minVal_le f b
  dsimp [capacity, osc]
  linarith

/-- The witness pair belongs to the challenger; every incumbent pair is bounded. -/
theorem range_ge_iff_exists_pair (f g : A → ℝ) :
    capacity f ≤ capacity g ↔
      ∃ a b : A, ∀ u v : A, f u - f v ≤ g a - g b := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := exists_eq_maxVal g
    obtain ⟨b, hb⟩ := exists_eq_minVal g
    refine ⟨a, b, fun u v => ?_⟩
    calc f u - f v ≤ capacity f := pair_le_capacity f u v
      _ ≤ capacity g := h
      _ = g a - g b := by unfold capacity osc; rw [← ha, ← hb]
  · rintro ⟨a, b, h⟩
    obtain ⟨u, hu⟩ := exists_eq_maxVal f
    obtain ⟨v, hv⟩ := exists_eq_minVal f
    calc capacity f = f u - f v := by unfold capacity osc; rw [← hu, ← hv]
      _ ≤ g a - g b := h u v
      _ ≤ capacity g := pair_le_capacity g a b

def ClosedAlternative (T : Finset R) (Q : R → A → ℝ) : Prop :=
  ∃ i ∈ T, ∃ j, j ∉ T ∧ capacity (Q i) ≤ capacity (Q j)

def PairRegion (Q : R → A → ℝ) (i j : R) (a b : A) : Prop :=
  ∀ u v : A, Q i u - Q i v ≤ Q j a - Q j b

/-- A strict top-k certificate fails exactly on the closed answer boundary. -/
theorem not_strictTopK_iff (T : Finset R) (k : ℕ) (hcard : T.card = k)
    (Q : R → A → ℝ) :
    ¬ StrictTopK (fun r => capacity (Q r)) T k ↔ ClosedAlternative T Q := by
  classical
  simp only [StrictTopK, hcard, true_and, ClosedAlternative]
  push_neg
  rfl

theorem alternative_union_polyhedra (T : Finset R) (Q : R → A → ℝ) :
    ClosedAlternative T Q ↔
      ∃ i ∈ T, ∃ j, j ∉ T ∧ ∃ a b : A, PairRegion Q i j a b := by
  constructor
  · rintro ⟨i, hi, j, hj, h⟩
    obtain ⟨a, b, hab⟩ := (range_ge_iff_exists_pair (Q i) (Q j)).mp h
    exact ⟨i, hi, j, hj, a, b, hab⟩
  · rintro ⟨i, hi, j, hj, a, b, hab⟩
    exact ⟨i, hi, j, hj, (range_ge_iff_exists_pair (Q i) (Q j)).mpr ⟨a, b, hab⟩⟩

/-- Each region is convex, with no definiteness assumption on an observation matrix. -/
theorem pairRegion_convex (i j : R) (a b : A) :
    Convex ℝ {Q : R → A → ℝ | PairRegion Q i j a b} := by
  intro Q hQ P hP alpha beta ha hb hab
  change PairRegion (alpha • Q + beta • P) i j a b
  intro u v
  have h1 := mul_le_mul_of_nonneg_left (hQ u v) ha
  have h2 := mul_le_mul_of_nonneg_left (hP u v) hb
  change alpha * Q i u + beta * P i u - (alpha * Q i v + beta * P i v) ≤
    alpha * Q j a + beta * P j a - (alpha * Q j b + beta * P j b)
  nlinarith

/-- Equality of attainable energy sets; applies to any real energy functional. -/
theorem energy_sets_equal (T : Finset R) (E : (R → A → ℝ) → ℝ) :
    {z : ℝ | ∃ Q, ClosedAlternative T Q ∧ E Q = z} =
      {z : ℝ | ∃ i ∈ T, ∃ j, j ∉ T ∧ ∃ a b : A,
        ∃ Q, PairRegion Q i j a b ∧ E Q = z} := by
  ext z
  constructor
  · rintro ⟨Q, hQ, hz⟩
    obtain ⟨i, hi, j, hj, a, b, hab⟩ := (alternative_union_polyhedra T Q).mp hQ
    exact ⟨i, hi, j, hj, a, b, Q, hab, hz⟩
  · rintro ⟨i, hi, j, hj, a, b, Q, hab, hz⟩
    exact ⟨Q, (alternative_union_polyhedra T Q).mpr ⟨i, hi, j, hj, a, b, hab⟩, hz⟩

/-- Rewriting the same energy set under sInf; no attainment is asserted. -/
theorem energy_inf_rewrite (T : Finset R) (E : (R → A → ℝ) → ℝ) :
    sInf {z : ℝ | ∃ Q, ClosedAlternative T Q ∧ E Q = z} =
      sInf {z : ℝ | ∃ i ∈ T, ∃ j, j ∉ T ∧ ∃ a b : A,
        ∃ Q, PairRegion Q i j a b ∧ E Q = z} := by
  rw [energy_sets_equal T E]

#print axioms pair_le_capacity
#print axioms range_ge_iff_exists_pair
#print axioms not_strictTopK_iff
#print axioms alternative_union_polyhedra
#print axioms pairRegion_convex
#print axioms energy_sets_equal
#print axioms energy_inf_rewrite

end CIGAMF.P13.FunctionalRangeAlternativeUnion
