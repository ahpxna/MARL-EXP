import Mathlib

/-! # Structural: the average/execution gap is at most the number of budgets, and
that bound is ATTAINED.

For a distribution `P` over orderings and a non-negative regret `r pi k`,

  `avgVal  = max_k  ∑_pi P pi * r pi k`      (guarantee ON AVERAGE, per budget)
  `pathVal = ∑_pi P pi * max_k r pi k`       (guarantee ON EXECUTION, per ordering)

`scripts/P3_avg_path_amplification.py` searches for instances where the ratio grows
with the number `b` of live budgets, and finds an explicit infinite family of
signed-scalar component tables

  `g_m = (-3, (-1)^(ceil (m-2)/2), (+1)^(floor (m-2)/2), 3)`,
  `eps_nest = 2/(m+4)`,  `V_avg = 2/((m+4)(m-1))`,  ratio `= m-1 = b`,

verified in exact rationals for `m = 5..14`, together with an exhaustive search
showing `b` is the BEST ratio available at every `m ≤ 7`.  This file proves the two
inequalities that turn those numbers into a statement, and the corollary that pins
the ratio exactly.

## WHAT IS PROVED

* `avg_le_path` — the execution guarantee is never better than the average one.
* `path_le_card_avg` — `pathVal ≤ b * avgVal` with `b = card Bud`: the universal
  upper bound, from `max_k r ≤ ∑_k r` for non-negative `r`.
* `eps_le_path` — `min_pi max_k r pi k ≤ pathVal` for any distribution `P`: no
  mixture can execute better than the best single ordering.
* `eps_le_card_avg` — hence `eps_nest ≤ b * avgVal`, i.e. `avgVal ≥ eps_nest / b`.
  This is the SATURATION LEMMA: it is why the ratio can never exceed `b`.
* `gap_exactly_card` — and when `b * avgVal = eps_nest` (which is what the family
  above achieves) the two bounds meet, so `pathVal = b * avgVal` EXACTLY.

## WHAT THIS DOES NOT ESTABLISH

- `r` here is an arbitrary non-negative function.  That the regret of the CIG-AMF
  `selectedRadius` construction has this shape, and the closed form of the family,
  are computed in the script, not formalised.
- The marginal constraint `M(P) = x` does not appear: these inequalities hold for
  every distribution `P`, which is what makes them usable on both sides of the
  constrained programmes, but it means nothing here is specific to a particular `x`.
- `eps_nest` is represented as `inf' over orderings of sup' over budgets` of the
  given `r`; no claim is made that this equals the paper's `eps_nest` for any
  particular component table.
-/

namespace CIGAMF.P13.StructuralAvgPathGap

open Finset

noncomputable section

variable {Ord Bud : Type*} [Fintype Ord] [Fintype Bud] [Nonempty Ord] [Nonempty Bud]

/-- The per-budget average guarantee. -/
def avgVal (r : Ord → Bud → ℝ) (P : Ord → ℝ) : ℝ :=
  (univ : Finset Bud).sup' univ_nonempty (fun k => ∑ pi, P pi * r pi k)

/-- The execution guarantee. -/
def pathVal (r : Ord → Bud → ℝ) (P : Ord → ℝ) : ℝ :=
  ∑ pi, P pi * ((univ : Finset Bud).sup' univ_nonempty (fun k => r pi k))

/-- The best single ordering: `eps_nest`. -/
def epsNest (r : Ord → Bud → ℝ) : ℝ :=
  (univ : Finset Ord).inf' univ_nonempty
    (fun pi => (univ : Finset Bud).sup' univ_nonempty (fun k => r pi k))

theorem avg_le_path (r : Ord → Bud → ℝ) (P : Ord → ℝ) (hP : ∀ pi, 0 ≤ P pi) :
    avgVal r P ≤ pathVal r P := by
  refine Finset.sup'_le _ _ fun k _ => ?_
  refine Finset.sum_le_sum fun pi _ => ?_
  exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun k => r pi k) (mem_univ k)) (hP pi)

theorem path_le_card_avg (r : Ord → Bud → ℝ) (P : Ord → ℝ)
    (hr : ∀ pi k, 0 ≤ r pi k) (hP : ∀ pi, 0 ≤ P pi) :
    pathVal r P ≤ (Fintype.card Bud : ℝ) * avgVal r P := by
  have step : pathVal r P ≤ ∑ pi, P pi * (∑ k, r pi k) := by
    refine Finset.sum_le_sum fun pi _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hP pi)
    refine Finset.sup'_le _ _ fun k _ => ?_
    exact Finset.single_le_sum (f := fun k => r pi k) (fun k _ => hr pi k) (mem_univ k)
  have swap : ∑ pi, P pi * (∑ k, r pi k) = ∑ k, ∑ pi, P pi * r pi k := by
    have inner : ∀ pi : Ord, P pi * (∑ k, r pi k) = ∑ k, P pi * r pi k :=
      fun pi => Finset.mul_sum _ _ _
    simp_rw [inner]
    exact Finset.sum_comm
  have bound : ∑ k, (∑ pi, P pi * r pi k) ≤ ∑ _k : Bud, avgVal r P :=
    Finset.sum_le_sum fun k _ => Finset.le_sup' (fun k => ∑ pi, P pi * r pi k) (mem_univ k)
  have card : ∑ _k : Bud, avgVal r P = (Fintype.card Bud : ℝ) * avgVal r P := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc pathVal r P ≤ ∑ pi, P pi * (∑ k, r pi k) := step
    _ = ∑ k, ∑ pi, P pi * r pi k := swap
    _ ≤ ∑ _k : Bud, avgVal r P := bound
    _ = (Fintype.card Bud : ℝ) * avgVal r P := card

theorem eps_le_path (r : Ord → Bud → ℝ) (P : Ord → ℝ)
    (hP : ∀ pi, 0 ≤ P pi) (hP1 : ∑ pi, P pi = 1) :
    epsNest r ≤ pathVal r P := by
  have : ∑ pi, P pi * epsNest r ≤ pathVal r P := by
    refine Finset.sum_le_sum fun pi _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hP pi)
    exact Finset.inf'_le _ (mem_univ pi)
  calc epsNest r = (∑ pi, P pi) * epsNest r := by rw [hP1, one_mul]
    _ = ∑ pi, P pi * epsNest r := by rw [Finset.sum_mul]
    _ ≤ pathVal r P := this

/-- THE SATURATION LEMMA.  The average guarantee can never be smaller than
`eps_nest / b`, so the ratio `pathVal / avgVal` can never exceed `b`. -/
theorem eps_le_card_avg (r : Ord → Bud → ℝ) (P : Ord → ℝ)
    (hr : ∀ pi k, 0 ≤ r pi k) (hP : ∀ pi, 0 ≤ P pi) (hP1 : ∑ pi, P pi = 1) :
    epsNest r ≤ (Fintype.card Bud : ℝ) * avgVal r P :=
  le_trans (eps_le_path r P hP hP1) (path_le_card_avg r P hr hP)

/-- When the two bounds meet -- which is exactly what the explicit family achieves --
the gap is EXACTLY the number of budgets. -/
theorem gap_exactly_card (r : Ord → Bud → ℝ) (P : Ord → ℝ)
    (hr : ∀ pi k, 0 ≤ r pi k) (hP : ∀ pi, 0 ≤ P pi) (hP1 : ∑ pi, P pi = 1)
    (hsat : (Fintype.card Bud : ℝ) * avgVal r P = epsNest r) :
    pathVal r P = (Fintype.card Bud : ℝ) * avgVal r P := by
  have h1 : epsNest r ≤ pathVal r P := eps_le_path r P hP hP1
  have h2 : pathVal r P ≤ (Fintype.card Bud : ℝ) * avgVal r P :=
    path_le_card_avg r P hr hP
  rw [hsat] at h2 ⊢
  exact le_antisymm h2 h1

#print axioms avgVal
#print axioms avg_le_path
#print axioms path_le_card_avg
#print axioms eps_le_path
#print axioms eps_le_card_avg
#print axioms gap_exactly_card

end
end CIGAMF.P13.StructuralAvgPathGap
