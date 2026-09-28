import «LeanPaperCFinalV1»

/-!
# Paper C: ranking → flow, the direction that was only described

`LeanPaperCFinalV1` closes flow → ranking: a layered flow is realised by an actual law over
rankings.  The other direction was written in prose.  It is not hard, but it has to be
written, because the reduction claim is an *equivalence* and an equivalence needs both ways.

WHAT CONSERVATION ACTUALLY IS.  Given a law `P` over rankings and the prefix composition at
each budget, put

    x_k(v)      = P( comp_k = v ),
    f_k(v, v')  = P( comp_k = v  and  comp_{k+1} = v' ).

Then `sum_{v'} f_k(v, v') = x_k(v)` and `sum_v f_k(v, v') = x_{k+1}(v')`.  Both are
**marginalisation of a joint distribution** — nothing about rankings, compositions or
budgets enters.  So the honest form of this lemma is the general one below, stated for any
finite law and any two observables; the flow is what one gets by naming the observables
`comp_k` and `comp_{k+1}`.

Stating it generally is not a dodge: it is what makes the step checkable.  The content of
"ranking → flow" is that the flow variables are marginals of one joint law, and the
conservation law is the statement that a joint distribution has consistent marginals.
-/

namespace CIGAMF.P13.PaperCFlow

open Finset

variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]

/-- The occupancy an observable induces from a law. -/
noncomputable def occ (P : R → ℝ) (c : R → V) (v : V) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => c x = v), P x

/-- The joint of two observables under the same law. -/
noncomputable def joint (P : R → ℝ) (c c' : R → V) (v v' : V) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => c x = v ∧ c' x = v'), P x

/-- **Conservation, outgoing.**  Summing the joint over the second coordinate returns the
first observable's occupancy. -/
theorem sum_joint_right (P : R → ℝ) (c c' : R → V) (v : V) :
    ∑ v' : V, joint P c c' v v' = occ P c v := by
  classical
  unfold joint occ
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hv : c x = v
  · have : ∀ v' : V, (if c x = v ∧ c' x = v' then P x else 0)
        = if c' x = v' then P x else 0 := by
      intro v'; simp [hv]
    rw [Finset.sum_congr rfl (fun v' _ => this v'),
        Finset.sum_ite_eq Finset.univ (c' x) (fun _ => P x),
        if_pos (Finset.mem_univ _), if_pos hv]
  · simp [hv]

/-- **Conservation, incoming.**  Summing over the first coordinate returns the second
observable's occupancy. -/
theorem sum_joint_left (P : R → ℝ) (c c' : R → V) (v' : V) :
    ∑ v : V, joint P c c' v v' = occ P c' v' := by
  classical
  unfold joint occ
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hv : c' x = v'
  · have : ∀ v : V, (if c x = v ∧ c' x = v' then P x else 0)
        = if c x = v then P x else 0 := by
      intro v; simp [hv]
    rw [Finset.sum_congr rfl (fun v _ => this v),
        Finset.sum_ite_eq Finset.univ (c x) (fun _ => P x),
        if_pos (Finset.mem_univ _), if_pos hv]
  · simp [hv]

/-- **The flow is non-negative when the law is.** -/
theorem joint_nonneg (P : R → ℝ) (hP : ∀ x, 0 ≤ P x) (c c' : R → V) (v v' : V) :
    0 ≤ joint P c c' v v' :=
  Finset.sum_nonneg (fun x _ => hP x)

/-- **The occupancy at any budget totals the law's mass**, so a probability law gives a unit
flow. -/
theorem sum_occ (P : R → ℝ) (c : R → V) :
    ∑ v : V, occ P c v = ∑ x : R, P x := by
  classical
  unfold occ
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_ite_eq Finset.univ (c x) (fun _ => P x), if_pos (Finset.mem_univ _)]

/-- **The objective transports.**  The expectation of any per-budget cost under the law
equals its expectation under the occupancy — which is what makes the flow formulation the
same optimisation problem and not merely a relaxation of it. -/
theorem expectation_via_occ (P : R → ℝ) (c : R → V) (g : V → ℝ) :
    ∑ x : R, P x * g (c x) = ∑ v : V, occ P c v * g v := by
  classical
  unfold occ
  simp only [Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have : ∀ v : V, (if c x = v then P x else 0) * g v
      = if c x = v then P x * g v else 0 := by
    intro v; by_cases h : c x = v <;> simp [h]
  rw [Finset.sum_congr rfl (fun v _ => this v),
      Finset.sum_ite_eq Finset.univ (c x) (fun v => P x * g v),
      if_pos (Finset.mem_univ _)]

/-! ## Audit -/

#print axioms sum_joint_right
#print axioms sum_joint_left
#print axioms joint_nonneg
#print axioms sum_occ
#print axioms expectation_via_occ

end CIGAMF.P13.PaperCFlow
