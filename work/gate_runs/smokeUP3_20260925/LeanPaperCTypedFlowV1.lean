import «LeanPaperCFlowBandJoinV1»
import «LeanPaperCStabilityEndgameV1»

/-!
# Paper C: the flow equivalence for every multiset of `d` weight types

The flow program of Theorem `thm:flow` was proved for the family `g_m` (four types
`-3, -1, 1, 3`). Its core, `banded_vectors_agree`, holds for any type map and any cost on count
states. This module instantiates it at the **physical signed-prefix regret of an arbitrary
typed multiset**:
* `d` types with weights `wt : Fin d → ℝ`, and items typed by `ty : Fin m → Fin d`, so
  `g = wt ∘ ty`;
* the per-budget optimum `b_k(g) = min_{|S| = k} |Σ_S g|` and the normaliser `‖g‖₁`, both
  computed from `g`.

**What is proved.**
* `typedCost_eq`: on a ranking, the count-state cost `(|Σ_τ wt_τ v_τ| - b_k(g)) / ‖g‖₁` of its
  prefix composition is exactly the normalised physical regret of `g`.
* `typed_flow_equivalence`: the budget vectors of band-feasible laws over all `m!` rankings are
  exactly the objective vectors of count-feasible banded flows over `CState d m`. Item
  marginals are kept by uniform relabelling within each type (`banded_vectors_agree`).
* `typed_banded_infima`: every functional of the budget vector, in particular
  `max_k E r_k`, has the same infimum on both sides.
* `card_state`: the state space has `(m+1)^d` points, so for a fixed number of types the flow
  program has size polynomial in `m`. This is a polynomial model for each fixed `d`, not a
  polynomial algorithm for arbitrary weights.
-/

namespace CIGAMF.P13.PaperCTypedFlow

open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCFlow
open CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCRankFlow
open CIGAMF.P13.PaperCFlowLaw CIGAMF.P13.PaperCNaming
open CIGAMF.P13.PaperCRelabel CIGAMF.P13.PaperCLawPush
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCFlowBandJoin CIGAMF.P13.PaperCStabilityEndgame

variable {d m : ℕ}

/-- The weights of a typed multiset. -/
def typedG (ty : Fin m → Fin d) (wt : Fin d → ℝ) : Fin m → ℝ := fun i => wt (ty i)

/-- **The physical signed-prefix cost of a count state.** -/
noncomputable def typedCost (ty : Fin m → Fin d) (wt : Fin d → ℝ) (k : Fin (m + 1))
    (v : CState d m) : ℝ :=
  (|∑ τ, wt τ * ((v τ).val : ℝ)| - trueBaseline (typedG ty wt) k) / normMass (typedG ty wt)

theorem prefixSet_sum_eq (g : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (k : Fin (m + 1)) :
    ∑ i ∈ prefixSet σ k, g i = prefixSum (rankOf g σ) k.val := by
  classical
  unfold prefixSet prefixSum rankOf
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Equiv.sum_comp σ (fun i => if ((σ.symm i : Fin m) : ℕ) < k.val then g i else 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Equiv.symm_apply_apply]

/-- **On a ranking, the count cost of its prefix composition is its physical regret.** -/
theorem typedCost_eq (ty : Fin m → Fin d) (wt : Fin d → ℝ) (σ : Equiv.Perm (Fin m))
    (k : Fin (m + 1)) :
    typedCost ty wt k (rankLayer ty k σ) = normalizedRegret (typedG ty wt) σ k := by
  unfold typedCost normalizedRegret rawRegret
  rw [typed_prefix_sum ty wt σ k, prefixSet_sum_eq]
  rfl

/-- **The flow equivalence for every typed multiset.** -/
theorem typed_flow_equivalence (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ) :
    {y : Fin (m + 1) → ℝ | ∃ P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η,
      (fun k => ∑ σ, P σ * normalizedRegret (typedG ty wt) σ k) = y}
      = {y | ∃ F, CountFeasibleH ty F ∧ FlowBand ty F η ∧ flowObj (typedCost ty wt) F = y} := by
  have hkey : ∀ P : Equiv.Perm (Fin m) → ℝ,
      rankObj ty (typedCost ty wt) P = fun k => ∑ σ, P σ * normalizedRegret (typedG ty wt) σ k := by
    intro P
    funext k
    unfold rankObj
    exact Finset.sum_congr rfl fun σ _ => by rw [typedCost_eq]
  convert banded_vectors_agree ty η (typedCost ty wt) using 1
  ext y
  simp only [hkey]

/-- **Every functional of the budget vector has the same infimum.** -/
theorem typed_banded_infima (ty : Fin m → Fin d) (wt : Fin d → ℝ) (η : ℝ)
    (Φ : (Fin (m + 1) → ℝ) → ℝ) :
    sInf (Φ '' {y : Fin (m + 1) → ℝ | ∃ P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η,
      (fun k => ∑ σ, P σ * normalizedRegret (typedG ty wt) σ k) = y})
      = sInf (Φ '' {y | ∃ F, CountFeasibleH ty F ∧ FlowBand ty F η
          ∧ flowObj (typedCost ty wt) F = y}) := by
  rw [typed_flow_equivalence]

/-- **The state space has `(m+1)^d` points.** -/
theorem card_state : Fintype.card (CState d m) = (m + 1) ^ d := by
  simp [CState]

/-- **The family is an instance**: its four types reproduce its weights. -/
theorem family_is_typed (m : ℕ) : typedG (familyType m) typeWeight = gFamily m := by
  funext i
  exact familyType_weight m i

#print axioms prefixSet_sum_eq
#print axioms typedCost_eq
#print axioms typed_flow_equivalence
#print axioms typed_banded_infima
#print axioms card_state
#print axioms family_is_typed

end CIGAMF.P13.PaperCTypedFlow
