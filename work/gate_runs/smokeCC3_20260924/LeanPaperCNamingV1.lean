import «LeanPaperCFlowV1»

/-!
# Paper C: the naming step — the flow variables at `comp_k`

`LeanPaperCFlowV1` proves conservation for an arbitrary finite law and an arbitrary pair of
observables, and says in its own header that the flow is what one gets *by naming the
observables* `comp_k` and `comp_{k+1}`.  That naming was the step left in prose.  It is
done here, at the layer map the rest of the corpus already uses: `rankLayer ty k`, the count
vector of the first `k` positions of a permutation by type.

So the objects are the paper's own,

    x_k(v) = P( rankLayer_k = v ),   f_k(v,v') = P( rankLayer_k = v and rankLayer_{k+1} = v' ),

and conservation, non-negativity, the unit total and the transport of the objective are
instances of the general statements rather than new arguments.  That is the point: the
content of ranking-to-flow is that the flow variables are marginals of one joint law, and
naming them changes nothing about why it is true.

**What the group occupancies do and do not give.**  `rankLayer` records how many items of
each *type* have been served, not which ones, so a per-item retained marginal is not a
function of the composition.  It becomes one only after relabelling within each type group,
which is the existing `relabelledLaw_invariant` / `marginal_eq_occupancy_div_card` route and
is not redone here.  What transports directly is the *group* occupancy, which is
`group_count_transports`.
-/

namespace CIGAMF.P13.PaperCNaming

open Finset
open CIGAMF.P13.PaperCFlow
open CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.CFinal

variable {d m : ℕ}

/-- The flow's state variable at budget `k`: the law's occupancy of the composition `v`. -/
noncomputable def flowX (P : Equiv.Perm (Fin m) → ℝ) (ty : Fin m → Fin d)
    (k : Fin (m + 1)) (v : CState d m) : ℝ :=
  occ P (rankLayer ty k) v

/-- The flow's edge variable from budget `k` to `k+1`. -/
noncomputable def flowF (P : Equiv.Perm (Fin m) → ℝ) (ty : Fin m → Fin d)
    (k : Fin m) (v v' : CState d m) : ℝ :=
  joint P (rankLayer ty k.castSucc) (rankLayer ty k.succ) v v'

/-- **Conservation, outgoing**, at the named observables. -/
theorem flow_conservation_out (P : Equiv.Perm (Fin m) → ℝ) (ty : Fin m → Fin d)
    (k : Fin m) (v : CState d m) :
    ∑ v' : CState d m, flowF P ty k v v' = flowX P ty k.castSucc v :=
  sum_joint_right P _ _ v

/-- **Conservation, incoming**, at the named observables. -/
theorem flow_conservation_in (P : Equiv.Perm (Fin m) → ℝ) (ty : Fin m → Fin d)
    (k : Fin m) (v' : CState d m) :
    ∑ v : CState d m, flowF P ty k v v' = flowX P ty k.succ v' :=
  sum_joint_left P _ _ v'

/-- A law's flow is non-negative. -/
theorem flowF_nonneg (P : Equiv.Perm (Fin m) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (ty : Fin m → Fin d) (k : Fin m) (v v' : CState d m) :
    0 ≤ flowF P ty k v v' :=
  joint_nonneg P hP _ _ v v'

theorem flowX_nonneg (P : Equiv.Perm (Fin m) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (ty : Fin m → Fin d) (k : Fin (m + 1)) (v : CState d m) :
    0 ≤ flowX P ty k v :=
  Finset.sum_nonneg (fun x _ => hP x)

/-- **A probability law gives a unit flow, at every budget.** -/
theorem flowX_total (P : Equiv.Perm (Fin m) → ℝ) (ty : Fin m → Fin d) (k : Fin (m + 1)) :
    ∑ v : CState d m, flowX P ty k v = ∑ x : Equiv.Perm (Fin m), P x :=
  sum_occ P _

/-- **The objective transports at the named observables.**  Any per-budget cost of the
composition has the same expectation under the law and under the flow, so the flow
formulation is the same optimisation and not a relaxation of it. -/
theorem objective_transports (P : Equiv.Perm (Fin m) → ℝ) (ty : Fin m → Fin d)
    (k : Fin (m + 1)) (g : CState d m → ℝ) :
    ∑ x : Equiv.Perm (Fin m), P x * g (rankLayer ty k x)
      = ∑ v : CState d m, flowX P ty k v * g v :=
  expectation_via_occ P _ g

/-- **The group counts transport.**  The expected number of served items of type `τ` at
budget `k` is a linear functional of `x_k` — this is the constraint side, in the only form
the composition supports. -/
theorem group_count_transports (P : Equiv.Perm (Fin m) → ℝ) (ty : Fin m → Fin d)
    (k : Fin (m + 1)) (τ : Fin d) :
    ∑ x : Equiv.Perm (Fin m), P x * ((rankLayer ty k x τ : ℕ) : ℝ)
      = ∑ v : CState d m, flowX P ty k v * ((v τ : ℕ) : ℝ) :=
  expectation_via_occ P _ (fun v : CState d m => ((v τ : ℕ) : ℝ))

/-- **The whole budget vector transports at once**, which is what "the same optimisation"
means when the objective is a maximum over budgets: the per-budget expectations agree
budget by budget, so their maxima agree. -/
theorem budget_vector_transports (P : Equiv.Perm (Fin m) → ℝ) (ty : Fin m → Fin d)
    (g : Fin (m + 1) → CState d m → ℝ) :
    ∀ k : Fin (m + 1),
      ∑ x : Equiv.Perm (Fin m), P x * g k (rankLayer ty k x)
        = ∑ v : CState d m, flowX P ty k v * g k v :=
  fun k => expectation_via_occ P _ (g k)

/-! ## Audit -/

#print axioms flow_conservation_out
#print axioms flow_conservation_in
#print axioms flowF_nonneg
#print axioms flowX_total
#print axioms objective_transports
#print axioms group_count_transports
#print axioms budget_vector_transports

end CIGAMF.P13.PaperCNaming
