import Mathlib

/-! # Structural: relaxing the marginals costs at most `‖y‖₁ τ`, as a theorem.

`scripts/S3_avg_path_certificate.py` verifies, in exact rational arithmetic and with no
optimizer in the checking path, that on the instance `F = [[0,-2],[0,1],[0,1],[0,1],[0,0]]`

  * `V_avg = 4/15` and `V_path = 7/15` are OPTIMA, each certified by a dual that is
    feasible over ALL 120 permutations with worst slack exactly `0`;
  * the `V_path` dual has `‖y‖₁ = 17/5`.

It then states a ROBUST separation: widening every marginal equality into a box of
half-width `τ` leaves `P` feasible, so `V_avg(τ) ≤ 4/15`, while the `V_path` dual
objective falls by at most `τ‖y‖₁`, so

    V_path(τ) - V_avg(τ)  ≥  1/5 - (17/5) τ,   positive for τ < 1/17.

That last step was an ARGUMENT from the checked certificate, not a theorem. This file
makes it a theorem.

WHAT IS PROVED HERE
* `relaxed_weak_duality` — the general fact, over an arbitrary finite index of
  permutations and an arbitrary finite index of marginal constraints: if a dual
  `(y, z)` is feasible for the exact programme, then for EVERY `P` that is a
  probability vector whose marginals sit within `τ` of the target `x`,
      `z + ⟪y, x⟫ - (∑ i, |y i|) * τ  ≤  ∑ π, P π * c π`.
  Nothing about the instance is used: no `120`, no `4/15`, no geometry.
* `relaxed_value_lower` — the same statement read as a lower bound on the relaxed
  optimal value.
* `robust_separation` — combining it with any upper bound `a` on the relaxed `V_avg`
  gives `V_path(τ) - V_avg(τ) ≥ (obj - a) - ‖y‖₁ τ` for every feasible relaxed `P`.
* `separation_instance` — the instance numbers `obj = 7/15`, `a = 4/15`,
  `‖y‖₁ = 17/5` give `≥ 1/5 - (17/5) τ`.
* `separation_positive` — that is `> 0` exactly when `τ < 1/17`.

## WHAT THIS DOES NOT ESTABLISH

- THE CERTIFICATE ITSELF IS A HYPOTHESIS HERE. `relaxed_weak_duality` takes dual
  feasibility as an assumption; it is NOT re-checked in Lean over the 120
  permutations. That check lives in `S3_avg_path_certificate.py`, in exact rationals,
  and this file does not import it. So the chain is: Lean proves the relaxation law,
  the script proves the instance is feasible with those numbers.
- `V_avg(τ) ≤ 4/15` is likewise a hypothesis (`havg`), discharged by the script
  observing that the unrelaxed `P` remains feasible when the box is widened.
- One instance. Nothing here says how the separation scales with the size of the
  problem, and `τ < 1/17` is a threshold for THIS certificate, not a universal one.
- Everything is over `ℚ`. No limits, no continuity, no algorithm.
-/

namespace CIGAMF.P13.StructuralRobustSeparation
open Finset
open scoped BigOperators
noncomputable section

variable {Ix M : Type*} [Fintype Ix] [Fintype M] [DecidableEq M]

/-- A dual point: multipliers on the marginal constraints and one on `∑ P = 1`. -/
structure Dual (M : Type*) where
  y : M → ℚ
  z : ℚ

/-- The dual objective at the target marginals `x`. -/
def dualObj (D : Dual M) (x : M → ℚ) : ℚ := D.z + ∑ i, D.y i * x i

/-- `‖y‖₁`. -/
def l1 (D : Dual M) : ℚ := ∑ i, |D.y i|

/-- Dual feasibility: every permutation's constraint holds. `a i p` is the coefficient
of the marginal constraint `i` at the permutation `p`, and `c p` its cost. -/
def Feasible (D : Dual M) (a : M → Ix → ℚ) (c : Ix → ℚ) : Prop :=
  ∀ p : Ix, D.z + ∑ i, D.y i * a i p ≤ c p

/-- THE RELAXATION LAW. Widening each marginal equality into a box of half-width `τ`
lowers the dual bound by at most `‖y‖₁ τ`, and by nothing else. -/
theorem relaxed_weak_duality (D : Dual M) (a : M → Ix → ℚ) (c : Ix → ℚ)
    (hfeas : Feasible D a c) (x : M → ℚ) (τ : ℚ) (hτ : 0 ≤ τ)
    (P : Ix → ℚ) (hP0 : ∀ p, 0 ≤ P p) (hP1 : ∑ p, P p = 1)
    (hmarg : ∀ i, |(∑ p, P p * a i p) - x i| ≤ τ) :
    dualObj D x - l1 D * τ ≤ ∑ p, P p * c p := by
  classical
  -- the dual bound, weighted by P
  have hstep : ∑ p, P p * (D.z + ∑ i, D.y i * a i p) ≤ ∑ p, P p * c p := by
    refine Finset.sum_le_sum (fun p _ => ?_)
    exact mul_le_mul_of_nonneg_left (hfeas p) (hP0 p)
  -- rewrite the left side
  have hexp : ∑ p, P p * (D.z + ∑ i, D.y i * a i p)
      = D.z + ∑ i, D.y i * (∑ p, P p * a i p) := by
    have h1 : ∑ p, P p * (D.z + ∑ i, D.y i * a i p)
        = (∑ p, P p) * D.z + ∑ p, ∑ i, P p * (D.y i * a i p) := by
      rw [Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [mul_add, Finset.mul_sum]
    rw [h1, hP1, one_mul, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => by ring)
  -- the marginal slack costs at most ‖y‖₁ τ
  have hslack : dualObj D x - l1 D * τ
      ≤ D.z + ∑ i, D.y i * (∑ p, P p * a i p) := by
    have hterm : ∀ i : M, D.y i * x i - |D.y i| * τ
        ≤ D.y i * (∑ p, P p * a i p) := by
      intro i
      have h := hmarg i
      have h1 : -τ ≤ (∑ p, P p * a i p) - x i := (abs_le.mp h).1
      have h2 : (∑ p, P p * a i p) - x i ≤ τ := (abs_le.mp h).2
      rcases le_total 0 (D.y i) with hy | hy
      · have hm : D.y i * (-τ) ≤ D.y i * ((∑ p, P p * a i p) - x i) :=
          mul_le_mul_of_nonneg_left h1 hy
        rw [abs_of_nonneg hy]
        nlinarith [hm]
      · have hm : D.y i * τ ≤ D.y i * ((∑ p, P p * a i p) - x i) :=
          mul_le_mul_of_nonpos_left h2 hy
        rw [abs_of_nonpos hy]
        nlinarith [hm]
    have := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset M)) => hterm i)
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at this
    unfold dualObj l1
    linarith
  linarith [hexp ▸ hstep, hslack]

/-- Read as a lower bound on the relaxed optimal value. -/
theorem relaxed_value_lower (D : Dual M) (a : M → Ix → ℚ) (c : Ix → ℚ)
    (hfeas : Feasible D a c) (x : M → ℚ) (τ : ℚ) (hτ : 0 ≤ τ)
    (v : ℚ) (P : Ix → ℚ) (hP0 : ∀ p, 0 ≤ P p) (hP1 : ∑ p, P p = 1)
    (hmarg : ∀ i, |(∑ p, P p * a i p) - x i| ≤ τ)
    (hv : ∑ p, P p * c p ≤ v) :
    dualObj D x - l1 D * τ ≤ v :=
  le_trans (relaxed_weak_duality D a c hfeas x τ hτ P hP0 hP1 hmarg) hv

/-- THE ROBUST SEPARATION, with the `V_avg` side supplied as a hypothesis. -/
theorem robust_separation (D : Dual M) (a : M → Ix → ℚ) (c : Ix → ℚ)
    (hfeas : Feasible D a c) (x : M → ℚ) (τ : ℚ) (hτ : 0 ≤ τ)
    (P : Ix → ℚ) (hP0 : ∀ p, 0 ≤ P p) (hP1 : ∑ p, P p = 1)
    (hmarg : ∀ i, |(∑ p, P p * a i p) - x i| ≤ τ)
    (avgVal : ℚ) (havg : avgVal ≤ dualObj D x) :
    (dualObj D x - avgVal) - l1 D * τ ≤ (∑ p, P p * c p) - avgVal := by
  have := relaxed_weak_duality D a c hfeas x τ hτ P hP0 hP1 hmarg
  linarith

/-- The instance numbers of `S3_avg_path_certificate.py`. -/
theorem separation_instance (D : Dual M) (a : M → Ix → ℚ) (c : Ix → ℚ)
    (hfeas : Feasible D a c) (x : M → ℚ) (τ : ℚ) (hτ : 0 ≤ τ)
    (P : Ix → ℚ) (hP0 : ∀ p, 0 ≤ P p) (hP1 : ∑ p, P p = 1)
    (hmarg : ∀ i, |(∑ p, P p * a i p) - x i| ≤ τ)
    (hobj : dualObj D x = 7/15) (hl1 : l1 D = 17/5) :
    (1:ℚ)/5 - (17/5) * τ ≤ (∑ p, P p * c p) - 4/15 := by
  have h := relaxed_weak_duality D a c hfeas x τ hτ P hP0 hP1 hmarg
  rw [hobj, hl1] at h
  linarith

/-- The threshold: the bound is strictly positive exactly below `1/17`. -/
theorem separation_positive (τ : ℚ) :
    0 < (1:ℚ)/5 - (17/5) * τ ↔ τ < 1/17 := by
  constructor
  · intro h; linarith
  · intro h; linarith

#print axioms relaxed_weak_duality
#print axioms relaxed_value_lower
#print axioms robust_separation
#print axioms separation_instance
#print axioms separation_positive

end
end CIGAMF.P13.StructuralRobustSeparation
