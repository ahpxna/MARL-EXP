import «LeanFunctionalRangeAlternativeUnionV1»

/-! # Functional F5: the energy oracle on the alternative union, and the inner QP.

`LeanFunctionalRangeAlternativeUnionV1` proves that the closed answer-changing boundary
for the group-RANGE target is exactly a union of convex pair regions
(`alternative_union_polyhedra`), and rewrites the energy infimum over that union
(`energy_inf_rewrite`).  Two things were left open there and are supplied here.

## 1. THE ORACLE IS A FINITE CHECK

`energy_lower_bound_iff`: a number `c` lower-bounds the energy over the WHOLE alternative
set if and only if it lower-bounds it on every pair region.  Since `T`, its complement and
the action set are finite, certifying the oracle is a finite conjunction of convex
problems -- no infimum over an infinite-dimensional set is ever taken, and no
`BddBelow`/`Nonempty` side condition is needed.  `energy_ge_of_pairwise` is the direction
an oracle actually uses.

## 2. THE INNER QP HAS A CLOSED FORM

`inner_qp_lower` and `inner_qp_attained`: on one pair region the binding constraint is a
single linear inequality in four coordinates with coefficients `(+1,-1,-1,+1)`.
Minimising a weighted quadratic subject to it costs exactly

    g² / (2 (1/w₁ + 1/w₂ + 1/w₃ + 1/w₄)),

the harmonic form, and the minimiser is exhibited.  This is the `pairV` shape of
`LeanFunctionalCrossoverLowerV1`, DERIVED for the range target rather than transported
from the Top-1 surrogate.  The proof is a completed square against the explicit
minimiser; no optimiser and no Lagrange multiplier theorem is invoked.

## WHAT THIS DOES NOT ESTABLISH

- The design primal/dual on the union and the setup-cost law are still open; this file
  supplies the inner problem and the finite reduction, not the outer allocation.
- `inner_qp_*` treats the single binding constraint.  A point of the pair region at which
  several constraints bind simultaneously is covered only through the lower bound, which
  holds for every feasible point, not through the attainment statement.
- Nothing here is a statement about P4/P26, which remain a SIDE model.
-/

namespace CIGAMF.P13.FunctionalRangeEnergyOracle

open Finset
open CIGAMF.P13.FunctionalRangeAlternativeUnion

variable {A R : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
  [Fintype R] [DecidableEq R]

/-- **The oracle is a finite check.**  A lower bound over the whole alternative set is
equivalent to a lower bound on each convex pair region. -/
theorem energy_lower_bound_iff (T : Finset R) (E : (R → A → ℝ) → ℝ) (c : ℝ) :
    (∀ Q : R → A → ℝ, ClosedAlternative T Q → c ≤ E Q) ↔
      (∀ i ∈ T, ∀ j, j ∉ T → ∀ a b : A,
        ∀ Q : R → A → ℝ, PairRegion Q i j a b → c ≤ E Q) := by
  constructor
  · intro h i hi j hj a b Q hQ
    exact h Q ((alternative_union_polyhedra T Q).mpr ⟨i, hi, j, hj, a, b, hQ⟩)
  · intro h Q hQ
    obtain ⟨i, hi, j, hj, a, b, hab⟩ := (alternative_union_polyhedra T Q).mp hQ
    exact h i hi j hj a b Q hab

/-- The direction an oracle uses: certify each pair region, conclude the whole set. -/
theorem energy_ge_of_pairwise (T : Finset R) (E : (R → A → ℝ) → ℝ) (c : ℝ)
    (hpair : ∀ i ∈ T, ∀ j, j ∉ T → ∀ a b : A,
      ∀ Q : R → A → ℝ, PairRegion Q i j a b → c ≤ E Q) :
    ∀ Q : R → A → ℝ, ClosedAlternative T Q → c ≤ E Q :=
  (energy_lower_bound_iff T E c).mpr hpair

/-- The harmonic constant of four positive precisions. -/
noncomputable def harm (w1 w2 w3 w4 : ℝ) : ℝ := 1/w1 + 1/w2 + 1/w3 + 1/w4

theorem harm_pos {w1 w2 w3 w4 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3)
    (h4 : 0 < w4) : 0 < harm w1 w2 w3 w4 := by
  unfold harm
  have := one_div_pos.mpr h1; have := one_div_pos.mpr h2
  have := one_div_pos.mpr h3; have := one_div_pos.mpr h4
  linarith

/-- **The inner QP, lower bound.**  Every feasible deviation costs at least the harmonic
value.  Proved by completing the square against the explicit minimiser; no optimiser and
no multiplier theorem is used. -/
theorem inner_qp_lower {w1 w2 w3 w4 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3)
    (h4 : 0 < w4) (g : ℝ) (hg : 0 ≤ g) (x1 x2 x3 x4 : ℝ)
    (hfeas : g ≤ x1 - x2 - x3 + x4) :
    g ^ 2 / (2 * harm w1 w2 w3 w4)
      ≤ (w1*x1^2 + w2*x2^2 + w3*x3^2 + w4*x4^2) / 2 := by
  have hSpos : 0 < harm w1 w2 w3 w4 := harm_pos h1 h2 h3 h4
  have hne1 : w1 ≠ 0 := ne_of_gt h1
  have hne2 : w2 ≠ 0 := ne_of_gt h2
  have hne3 : w3 ≠ 0 := ne_of_gt h3
  have hne4 : w4 ≠ 0 := ne_of_gt h4
  have hSne : harm w1 w2 w3 w4 ≠ 0 := ne_of_gt hSpos
  have hid : w1*(x1 - g/(harm w1 w2 w3 w4*w1))^2
      + w2*(x2 + g/(harm w1 w2 w3 w4*w2))^2
      + w3*(x3 + g/(harm w1 w2 w3 w4*w3))^2
      + w4*(x4 - g/(harm w1 w2 w3 w4*w4))^2
      = (w1*x1^2 + w2*x2^2 + w3*x3^2 + w4*x4^2)
        - 2*(g/harm w1 w2 w3 w4)*(x1 - x2 - x3 + x4)
        + g^2/harm w1 w2 w3 w4 := by
    unfold harm at hSne ⊢
    field_simp
    ring
  have hnn : 0 ≤ w1*(x1 - g/(harm w1 w2 w3 w4*w1))^2
      + w2*(x2 + g/(harm w1 w2 w3 w4*w2))^2
      + w3*(x3 + g/(harm w1 w2 w3 w4*w3))^2
      + w4*(x4 - g/(harm w1 w2 w3 w4*w4))^2 := by
    have a1 : 0 ≤ w1*(x1 - g/(harm w1 w2 w3 w4*w1))^2 := mul_nonneg h1.le (sq_nonneg _)
    have a2 : 0 ≤ w2*(x2 + g/(harm w1 w2 w3 w4*w2))^2 := mul_nonneg h2.le (sq_nonneg _)
    have a3 : 0 ≤ w3*(x3 + g/(harm w1 w2 w3 w4*w3))^2 := mul_nonneg h3.le (sq_nonneg _)
    have a4 : 0 ≤ w4*(x4 - g/(harm w1 w2 w3 w4*w4))^2 := mul_nonneg h4.le (sq_nonneg _)
    linarith
  rw [hid] at hnn
  have hq : 0 ≤ g/harm w1 w2 w3 w4 := div_nonneg hg hSpos.le
  have hstep := mul_le_mul_of_nonneg_left hfeas hq
  have hrw : (g/harm w1 w2 w3 w4)*g = g^2/harm w1 w2 w3 w4 := by
    field_simp
    try ring
  rw [hrw] at hstep
  have hmain : g^2/harm w1 w2 w3 w4 ≤ w1*x1^2 + w2*x2^2 + w3*x3^2 + w4*x4^2 := by
    linarith
  have hsplit : g^2/(2*harm w1 w2 w3 w4) = (g^2/harm w1 w2 w3 w4)/2 := by
    rw [mul_comm, ← div_div]
  rw [hsplit]
  linarith

/-- **The inner QP, attainment.**  The harmonic value is achieved, so the lower bound is
exact and the constant cannot be improved. -/
theorem inner_qp_attained {w1 w2 w3 w4 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3)
    (h4 : 0 < w4) (g : ℝ) :
    ∃ x1 x2 x3 x4 : ℝ, g ≤ x1 - x2 - x3 + x4 ∧
      (w1*x1^2 + w2*x2^2 + w3*x3^2 + w4*x4^2) / 2
        = g ^ 2 / (2 * harm w1 w2 w3 w4) := by
  have hSpos : 0 < harm w1 w2 w3 w4 := harm_pos h1 h2 h3 h4
  have hne1 : w1 ≠ 0 := ne_of_gt h1
  have hne2 : w2 ≠ 0 := ne_of_gt h2
  have hne3 : w3 ≠ 0 := ne_of_gt h3
  have hne4 : w4 ≠ 0 := ne_of_gt h4
  have hSne : harm w1 w2 w3 w4 ≠ 0 := ne_of_gt hSpos
  refine ⟨g/(harm w1 w2 w3 w4*w1), -(g/(harm w1 w2 w3 w4*w2)),
          -(g/(harm w1 w2 w3 w4*w3)), g/(harm w1 w2 w3 w4*w4), ?_, ?_⟩
  · have hsum : g/(harm w1 w2 w3 w4*w1) - -(g/(harm w1 w2 w3 w4*w2))
        - -(g/(harm w1 w2 w3 w4*w3)) + g/(harm w1 w2 w3 w4*w4) = g := by
      unfold harm at hSne ⊢
      field_simp
      ring
    exact le_of_eq hsum.symm
  · unfold harm at hSne ⊢
    field_simp
    try ring

#print axioms energy_lower_bound_iff
#print axioms energy_ge_of_pairwise
#print axioms harm_pos
#print axioms inner_qp_lower
#print axioms inner_qp_attained

end CIGAMF.P13.FunctionalRangeEnergyOracle
