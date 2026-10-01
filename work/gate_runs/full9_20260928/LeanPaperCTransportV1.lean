import «LeanPaperCFlowV1»

/-!
# Paper C: the reduction transports the WHOLE budget vector, and the band with it

`LeanPaperCFlowV1` shows the flow variables are marginals of one joint law and that a single
per-budget cost transports.  The reduction claim is stronger than that and has to be stated
as such: the optimisation is over the maximum across budgets and under the marginal band, so
what must transport is the **entire vector** of per-budget values and the **constraints**,
not one coordinate of the objective.

Both follow from the single-observable statement, but only once the right hypothesis is
named.  A per-item membership indicator is a function of the prefix COMPOSITION exactly when
items of the same type are interchangeable; that factorisation is a genuine hypothesis about
the model and is carried explicitly below rather than absorbed into notation.
-/

namespace CIGAMF.P13.PaperCTransport

open Finset
open CIGAMF.P13.PaperCFlow

variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]

/-- **Every budget's value transports at once.**  The whole vector, not one coordinate. -/
theorem vector_transports {K : Type*} [Fintype K]
    (P : R → ℝ) (c : K → R → V) (g : K → V → ℝ) :
    ∀ k : K, ∑ x : R, P x * g k (c k x) = ∑ v : V, occ P (c k) v * g k v :=
  fun k => expectation_via_occ P (c k) (g k)

/-- **Hence the maximum over budgets transports.**  The objective of Paper C is
`max_k E[r_k]`, so this is the step that makes the flow formulation the same optimisation
and not a relaxation of it. -/
theorem sup_transports {K : Type*} [Fintype K] [Nonempty K] [DecidableEq K]
    (P : R → ℝ) (c : K → R → V) (g : K → V → ℝ) :
    (Finset.univ : Finset K).sup' Finset.univ_nonempty (fun k => ∑ x : R, P x * g k (c k x))
      = (Finset.univ : Finset K).sup' Finset.univ_nonempty
          (fun k => ∑ v : V, occ P (c k) v * g k v) :=
  Finset.sup'_congr _ rfl (fun k _ => vector_transports P c g k)

/-- **The marginal constraint transports too**, under the hypothesis that makes it a
statement about compositions: a per-item membership indicator is a function of the prefix
composition exactly when items of a type are interchangeable.  That hypothesis is named. -/
theorem marginal_transports (P : R → ℝ) (c : R → V) (memb : R → ℝ) (φ : V → ℝ)
    (hfac : ∀ x : R, memb x = φ (c x)) :
    ∑ x : R, P x * memb x = ∑ v : V, occ P c v * φ v := by
  have h : ∀ x : R, P x * memb x = P x * φ (c x) := fun x => by rw [hfac x]
  rw [Finset.sum_congr rfl (fun x _ => h x)]
  exact expectation_via_occ P c φ

/-- **A band on the law is a band on the occupancy**, and conversely --- so a feasible law
gives a feasible flow with the same constraint, which is what an equivalence of the two
optimisation problems needs. -/
theorem band_transports (P : R → ℝ) (c : R → V) (memb : R → ℝ) (φ : V → ℝ) (lo hi : ℝ)
    (hfac : ∀ x : R, memb x = φ (c x)) :
    (lo ≤ ∑ x : R, P x * memb x ∧ ∑ x : R, P x * memb x ≤ hi)
      ↔ (lo ≤ ∑ v : V, occ P c v * φ v ∧ ∑ v : V, occ P c v * φ v ≤ hi) := by
  rw [marginal_transports P c memb φ hfac]

/-! ## Audit -/

#print axioms vector_transports
#print axioms sup_transports
#print axioms marginal_transports
#print axioms band_transports

end CIGAMF.P13.PaperCTransport
