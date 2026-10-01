import «LeanPaperCEndpointLawV1»
import «LeanPaperCFlowBandJoinV1»

/-!
# Paper C: the flow formulation, at the paper's own objective

`actual_banded_infima` (`LeanPaperCFlowBandJoinV1`) says that for ANY functional `Phi` of the
budget vector, the infimum over band-feasible laws on all permutations equals the infimum
over band-feasible type flows.  A theorem about an arbitrary `Phi` is not yet the paper's
statement.  This module instantiates `Phi` with the paper's objective -- the worst expected
regret over the interior budgets `1, ..., m-1` -- and shows that the flow infimum IS the
value `value m eta` of `LeanPaperCEndgameV1`.  Both directions of the underlying equivalence
carry every band constraint and the whole budget vector; nothing is lost in the instantiation
because the paper's objective is a function of that vector.

With the endpoint laws of `LeanPaperCEndpointLawV1`, the two headline results then hold on
the flow side as well: the even frontier for every even `m >= 4` and the odd breakpoint for
every odd `m >= 3`.  This is a statement about the VALUE of the flow program; it makes no
claim about an efficient algorithm for perturbed item weights, which the four-type flow does
not cover.
-/

namespace CIGAMF.P13.PaperCFlowObjective

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCFlowBandJoin
open CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCFlowLaw CIGAMF.P13.PaperCEndpointLaw

/-- **The paper's objective, read off a budget vector**: the worst interior budget. -/
noncomputable def worstInterior (m : ℕ) (hm : 2 ≤ m) (y : Fin (m + 1) → ℝ) : ℝ :=
  (budgets m).sup' (budgets_nonempty m hm) (fun k => if hk : k < m + 1 then y ⟨k, hk⟩ else 0)

/-- The objective of a law is the worst interior budget of its expected-regret vector. -/
theorem objective_eq_worstInterior (m : ℕ) (hm : 2 ≤ m) (P : Equiv.Perm (Fin m) → ℝ) :
    objective m hm P
      = worstInterior m hm (fun k => ∑ σ, P σ * regret (gFamily m) σ (denom m) k.val) := by
  unfold objective maxRegret worstInterior
  refine Finset.sup'_congr _ rfl fun k hk => ?_
  have hk' : k < m + 1 := by
    have := (Finset.mem_Icc.mp (by simpa [budgets] using hk) : 1 ≤ k ∧ k ≤ m - 1)
    omega
  rw [dif_pos hk']
  rfl

/-- **The value of the paper's program is the value of the flow program**, with the
objective instantiated -- not an arbitrary functional. -/
theorem value_eq_flow (m : ℕ) (hm : 2 ≤ m) (η : ℝ) :
    value m hm η
      = sInf (worstInterior m hm ''
          {y | ∃ F, CountFeasibleH (familyType m) F ∧ FlowBand (familyType m) F η ∧
            flowObj (signedCost (denom m)) F = y}) := by
  rw [← actual_banded_infima (m := m) (denom m) η (worstInterior m hm)]
  unfold value Vm
  congr 1
  ext v
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨_, ⟨P, hP, rfl⟩, (objective_eq_worstInterior m hm P).symm⟩
  · rintro ⟨y, ⟨P, hP, rfl⟩, rfl⟩
    exact ⟨P, hP, objective_eq_worstInterior m hm P⟩

/-- **The even frontier, on the flow side**, for every even `m >= 4`. -/
theorem even_frontier_flow (m : ℕ) (hm : 4 ≤ m) (heven : Even m) (η : ℝ) (hη : 0 ≤ η) :
    sInf (worstInterior m (by omega) ''
        {y | ∃ F, CountFeasibleH (familyType m) F ∧ FlowBand (familyType m) F η ∧
          flowObj (signedCost (denom m)) F = y})
      = max (freeValue m) (4 * (1 - η) / ((m : ℝ) * denom m)) := by
  rw [← value_eq_flow m (by omega) η]
  exact even_frontier_all m hm heven η hη

/-- **The odd breakpoint, on the flow side**, for every odd `m >= 3`. -/
theorem odd_breakpoint_flow (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) (η : ℝ) (hη : 0 ≤ η) :
    sInf (worstInterior m (by omega) ''
        {y | ∃ F, CountFeasibleH (familyType m) F ∧ FlowBand (familyType m) F η ∧
          flowObj (signedCost (denom m)) F = y}) = freeValue m ↔ 1 ≤ η := by
  rw [← value_eq_flow m (by omega) η]
  exact odd_breakpoint m hm hmo η hη

#print axioms objective_eq_worstInterior
#print axioms value_eq_flow
#print axioms even_frontier_flow
#print axioms odd_breakpoint_flow

end CIGAMF.P13.PaperCFlowObjective
