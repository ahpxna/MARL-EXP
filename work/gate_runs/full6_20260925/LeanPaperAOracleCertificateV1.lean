import Mathlib

/-!
# Paper A: certifying the compression oracle globally, and certifying the design.

## WHY THIS MODULE EXISTS

The alternative set of a compression decision decomposes into finitely many polyhedral
regions, and on each one the information distance is a convex quadratic.  A grid search
can find a good candidate on each region; it cannot prove that the candidate is the
minimum, and refining only the region that won on the grid proves nothing at all about
the others.  Likewise, optimising the design inside a parametric family of allocations
does not show the allocation is optimal among ALL allocations.

This module supplies the two certificates that close those gaps.  Both are stated so that
a worker can emit numbers and have them checked, rather than asserting an optimum.

* `kkt_certifies_region_minimum` (step A3) -- a primal point together with non-negative
  multipliers satisfying stationarity and complementary slackness proves that the point
  minimises the quadratic over its region, for EVERY feasible competitor.  The proof is
  the exact expansion
  `f(z) - f(lam) = (1/2)(z-lam)^T H (z-lam) - y^T A (z-lam)`,
  whose two terms are non-negative for the two separate reasons recorded below.
* `design_upper_bound_of_dual` (step A4) -- a finite set of alternatives and a prior on
  them whose averaged per-query information is dominated by `V` times the query cost
  bounds EVERY admissible design by `V`.  Combined with a primal allocation attaining `V`
  this closes `sup_w J(w) = V` over all designs, not over a parametric family.
* `certification_costs_at_least_as_much` (step A6) -- if the certificate condition is
  sufficient for safety, its alternative set contains the decision's, so the certificate's
  information rate is no larger: certifying is never cheaper than deciding.

## WHAT IS PROVED

Everything above, for arbitrary finite dimension, arbitrary polyhedron and arbitrary
positive-semidefinite `H`.  `H` is NOT required to be invertible, which matters because a
design that leaves a direction unmeasured produces a singular `H`.

## WHAT THIS DOES NOT ESTABLISH

- **The region decomposition itself is not here.**  That the alternative set equals the
  union of the regions, with the strict inequality handled correctly, is step A2 and is
  proved elsewhere; this module certifies a minimum on a region that is given to it.
- **Nothing is claimed about finding the certificate.**  These are verification theorems.
  The multipliers come from a solver and are checked, which is the point.
- The dual bound needs the alternatives it quotes to be genuine alternatives; that
  membership is a hypothesis here (`hJ`), discharged by A2 in use.
- `certification_costs_at_least_as_much` is a comparison of information rates, not of
  expected sample counts; converting it needs a matching stopping theorem.
-/

set_option maxHeartbeats 1000000

namespace CIGAMF.P13.PaperAOracleCertificate

open Finset

/-! ### Finite-dimensional linear algebra, by explicit sums -/

variable {n p : ℕ}

/-- The Euclidean pairing. -/
def dot (v w : Fin n → ℝ) : ℝ := ∑ i, v i * w i

/-- A row of `A v`. -/
def rowMul (A : Fin p → Fin n → ℝ) (v : Fin n → ℝ) (i : Fin p) : ℝ :=
  ∑ j, A i j * v j

/-- `H v`. -/
def matMul (H : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, H i j * v j

/-- The quadratic form `v^T H v`. -/
def quad (H : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : ℝ := dot v (matMul H v)

theorem dot_comm (v w : Fin n → ℝ) : dot v w = dot w v := by
  unfold dot
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_add_left (u v w : Fin n → ℝ) :
    dot (fun i => u i + v i) w = dot u w + dot v w := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_add_right (u v w : Fin n → ℝ) :
    dot u (fun i => v i + w i) = dot u v + dot u w := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem matMul_add (H : Fin n → Fin n → ℝ) (u v : Fin n → ℝ) :
    matMul H (fun i => u i + v i) = fun i => matMul H u i + matMul H v i := by
  funext i
  unfold matMul
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- With `H` symmetric, the two cross terms of the expansion agree. -/
theorem cross_symm (H : Fin n → Fin n → ℝ) (hsym : ∀ i j, H i j = H j i)
    (u v : Fin n → ℝ) : dot u (matMul H v) = dot v (matMul H u) := by
  unfold dot matMul
  have e1 : ∀ i, u i * ∑ j, H i j * v j = ∑ j, u i * H i j * v j := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∀ j, v j * ∑ i, H j i * u i = ∑ i, v j * H j i * u i := by
    intro j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e1, e2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hsym i j]
  ring

/-- **The exact expansion of a quadratic around a point.** -/
theorem quad_expand (H : Fin n → Fin n → ℝ) (hsym : ∀ i j, H i j = H j i)
    (u w : Fin n → ℝ) :
    quad H (fun i => u i + w i) = quad H u + 2 * dot w (matMul H u) + quad H w := by
  unfold quad
  rw [matMul_add, dot_add_left, dot_add_right, dot_add_right]
  have h1 : dot u (matMul H w) = dot w (matMul H u) := cross_symm H hsym u w
  linarith [h1]

/-! ### A3: the KKT certificate for one region -/

/-- The objective on a region: half the `H`-energy of the displacement from `theta`. -/
noncomputable def energy (H : Fin n → Fin n → ℝ) (theta lam : Fin n → ℝ) : ℝ :=
  quad H (fun i => lam i - theta i) / 2

/-- **A primal point with multipliers certifies the region minimum.**

`lam` is feasible, `y` is non-negative, stationarity `H(lam - theta) + A^T y = 0` holds and
the multipliers are complementary.  Then no feasible `z` does better.  `H` is only assumed
symmetric positive semidefinite: a design leaving a direction unmeasured gives a singular
`H`, and the statement must survive that. -/
theorem kkt_region_minimum
    (H : Fin n → Fin n → ℝ) (A : Fin p → Fin n → ℝ) (bvec : Fin p → ℝ)
    (theta lam : Fin n → ℝ) (y : Fin p → ℝ)
    (hsym : ∀ i j, H i j = H j i)
    (hpsd : ∀ v : Fin n → ℝ, 0 ≤ quad H v)
    (hfeas : ∀ i, rowMul A lam i ≤ bvec i)
    (hy : ∀ i, 0 ≤ y i)
    (hstat : ∀ j, matMul H (fun t => lam t - theta t) j + ∑ i, y i * A i j = 0)
    (hcs : ∀ i, y i * (rowMul A lam i - bvec i) = 0)
    (z : Fin n → ℝ) (hz : ∀ i, rowMul A z i ≤ bvec i) :
    energy H theta lam ≤ energy H theta z := by
  classical
  set u : Fin n → ℝ := fun t => lam t - theta t with hu
  set w : Fin n → ℝ := fun t => z t - lam t with hw
  -- the displacement of `z` splits through `lam`
  have hsplit : (fun t => z t - theta t) = fun t => u t + w t := by
    funext t; simp [hu, hw]
  -- the exact expansion
  have hexp : quad H (fun t => z t - theta t)
      = quad H u + 2 * dot w (matMul H u) + quad H w := by
    rw [hsplit]; exact quad_expand H hsym u w
  -- stationarity turns the cross term into a multiplier pairing
  have hstat' : ∀ j, matMul H u j = -∑ i, y i * A i j := by
    intro j
    have := hstat j
    linarith
  have hcross : dot w (matMul H u) = -∑ i, y i * rowMul A w i := by
    have e1 : dot w (matMul H u) = ∑ j, ∑ i, -(y i * A i j * w j) := by
      unfold dot
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hstat' j, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : (∑ j, ∑ i, -(y i * A i j * w j)) = ∑ i, -(y i * rowMul A w i) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold rowMul
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2, Finset.sum_neg_distrib]
  -- each multiplier pairing is non-positive on the feasible set
  have hterm : ∀ i, y i * rowMul A w i ≤ 0 := by
    intro i
    have hlin : rowMul A w i = rowMul A z i - rowMul A lam i := by
      unfold rowMul
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp [hw]; ring
    have hslack : y i * rowMul A lam i = y i * bvec i := by
      have h := hcs i
      have : y i * rowMul A lam i - y i * bvec i = 0 := by
        rw [← mul_sub]; exact h
      linarith
    rw [hlin, mul_sub, hslack]
    have : y i * rowMul A z i ≤ y i * bvec i :=
      mul_le_mul_of_nonneg_left (hz i) (hy i)
    linarith
  have hsum : ∑ i, y i * rowMul A w i ≤ 0 :=
    Finset.sum_nonpos fun i _ => hterm i
  -- assemble
  unfold energy
  have hq : 0 ≤ quad H w := hpsd w
  rw [hexp]
  linarith [hcross, hsum, hq]

/-! ### A4: optimality over EVERY design -/

/-- **A dual certificate over the whole query set bounds every admissible design.**

`d e l` is the per-sample information that query `e` carries against alternative `l`.  If
a prior `nu` on the alternatives makes the averaged information at most `V` times the
query's cost, for every query, then no allocation of unit budget can exceed `V`.  The
hypothesis `hJ` says `J` is a lower bound on the value at each quoted alternative, which
is what being an infimum over a set containing them provides. -/
theorem design_upper_bound_of_dual {E s : ℕ}
    (d : Fin E → Fin s → ℝ) (nu : Fin s → ℝ) (c w : Fin E → ℝ) (V J : ℝ)
    (hnu : ∀ l, 0 ≤ nu l) (hnusum : ∑ l, nu l = 1)
    (hw : ∀ e, 0 ≤ w e) (hbudget : ∑ e, c e * w e = 1)
    (hdual : ∀ e, ∑ l, nu l * d e l ≤ V * c e)
    (hJ : ∀ l, J ≤ ∑ e, w e * d e l) :
    J ≤ V := by
  classical
  -- J is below the prior average of the alternatives' values
  have h1 : J ≤ ∑ l, nu l * (∑ e, w e * d e l) := by
    have : ∑ l, nu l * J ≤ ∑ l, nu l * (∑ e, w e * d e l) :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hJ l) (hnu l)
    rwa [← Finset.sum_mul, hnusum, one_mul] at this
  -- exchange the two sums
  have h2 : ∑ l, nu l * (∑ e, w e * d e l) = ∑ e, w e * (∑ l, nu l * d e l) := by
    have e1 : ∀ l, nu l * (∑ e, w e * d e l) = ∑ e, nu l * w e * d e l := by
      intro l
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    have e2 : ∀ e, w e * (∑ l, nu l * d e l) = ∑ l, nu l * w e * d e l := by
      intro e
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    simp_rw [e1, e2]
    exact Finset.sum_comm
  -- and apply the dual inequality query by query
  have h3 : ∑ e, w e * (∑ l, nu l * d e l) ≤ ∑ e, w e * (V * c e) :=
    Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hdual e) (hw e)
  have h4 : ∑ e, w e * (V * c e) = V := by
    have : ∑ e, w e * (V * c e) = V * ∑ e, c e * w e := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [this, hbudget, mul_one]
  rw [h2] at h1
  linarith [h1, h3, h4]

/-- **Primal and dual meeting is optimality over all designs.** -/
theorem design_value_eq_of_primal_dual {E s : ℕ}
    (d : Fin E → Fin s → ℝ) (nu : Fin s → ℝ) (c : Fin E → ℝ) (V : ℝ)
    (Jof : (Fin E → ℝ) → ℝ)
    (hnu : ∀ l, 0 ≤ nu l) (hnusum : ∑ l, nu l = 1)
    (hdual : ∀ e, ∑ l, nu l * d e l ≤ V * c e)
    (hlower : ∀ w : Fin E → ℝ, (∀ e, 0 ≤ w e) → (∑ e, c e * w e = 1) →
      ∀ l, Jof w ≤ ∑ e, w e * d e l)
    (wstar : Fin E → ℝ) (hwnn : ∀ e, 0 ≤ wstar e) (hwb : ∑ e, c e * wstar e = 1)
    (hprimal : V ≤ Jof wstar) :
    Jof wstar = V ∧ ∀ w : Fin E → ℝ, (∀ e, 0 ≤ w e) → (∑ e, c e * w e = 1) →
      Jof w ≤ V := by
  refine ⟨le_antisymm ?_ hprimal, ?_⟩
  · exact design_upper_bound_of_dual d nu c wstar V (Jof wstar) hnu hnusum hwnn hwb
      hdual (hlower wstar hwnn hwb)
  · intro w hwn hwbud
    exact design_upper_bound_of_dual d nu c w V (Jof w) hnu hnusum hwn hwbud hdual
      (hlower w hwn hwbud)

/-! ### A6: certifying is never cheaper than deciding -/

/-- **A sufficient certificate has a larger alternative set, hence a smaller rate.**

If every world satisfying the certificate condition is one where `T` is safe, then every
world where `T` is unsafe fails the certificate: the decision's alternatives sit inside the
certificate's.  Taking infima reverses the inclusion. -/
theorem certification_costs_at_least_as_much
    {W : Type*} (safe cert : W → Prop) (info : W → ℝ) (Gd Gc : ℝ)
    (hsuff : ∀ x, cert x → safe x)
    (hGd : IsGLB {r : ℝ | ∃ x, ¬ safe x ∧ info x = r} Gd)
    (hGc : IsGLB {r : ℝ | ∃ x, ¬ cert x ∧ info x = r} Gc) :
    Gc ≤ Gd := by
  apply hGd.2
  intro r hr
  obtain ⟨x, hxs, rfl⟩ := hr
  exact hGc.1 ⟨x, fun hc => hxs (hsuff x hc), rfl⟩

#print axioms quad_expand
#print axioms kkt_region_minimum
#print axioms design_upper_bound_of_dual
#print axioms design_value_eq_of_primal_dual
#print axioms certification_costs_at_least_as_much

end CIGAMF.P13.PaperAOracleCertificate
