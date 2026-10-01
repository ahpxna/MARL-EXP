import «LeanPaperCOddBreakpointEndgameV1»
import «LeanPaperCEvenTotalV1»

/-!
# Paper C: `EvenEndpointData.rankSum`, discharged

`EvenEndpointData` (`LeanPaperCEndgameV1`) has three fields, and `even_frontier` consumes all
three.  Two are about ONE law -- an endpoint law that is band-feasible at `etaStar m` and
whose objective is at most the free value -- but the third, `rankSum`, is a statement about
EVERY relabelling of `g_m` and has nothing to do with that law:

    rankSum : forall sigma, 2 / denom m <= sum over budgets of regret (gFamily m) sigma _ k.

This module proves it, so the structure is reduced from three obligations to one.

The proof is a join of two things that already exist and one that did not.  What existed:
`total_eq_sum_regret` (`LeanPaperCOddBreakpointEndgameV1`) is generic in `m` and identifies
the budget sum with `totalExcess (rankOf (gFamily m) sigma) / denom m`.  What did not exist
until `LeanPaperCEvenTotalV1`: the EVEN total-excess inequality.  `odd_total_excess` covers
only families summing to `-1`, so the even side had no counterpart and that is precisely why
`rankSum` was left open rather than proved.

Note the import direction.  `total_eq_sum_regret` lives in the odd-breakpoint module, which
itself imports `LeanPaperCEndgameV1`, so this join CANNOT be placed inside `CEndgame` where
`EvenEndpointData` is declared -- it has to sit downstream of both. That is why the field is
discharged by `evenEndpointData_of_law` here rather than by changing the structure.
-/

namespace CIGAMF.P13.PaperCEvenRankSum

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCEndgame
open CIGAMF.P13.PaperCOddBreakpointEndgame CIGAMF.P13.PaperCEvenTotal

/-- Relabelling preserves the even family, exactly as `ranked_odd` does for the odd one. -/
theorem ranked_even (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) (σ : Perm m) :
    IsEvenFamily (rankOf (gFamily m) σ) := by
  have hf : IsEvenFamily (gFamily m) := by
    have hev := gFamily_isEvenFamily (m - 2) (by omega) (by omega)
    rwa [show m - 2 + 2 = m from by omega] at hev
  refine ⟨fun i => gFamily_weights m (σ i), ?_⟩
  change (∑ i, gFamily m (σ i)) = 0
  rw [Equiv.sum_comp σ]
  exact hf.total

/-- **The `rankSum` field, for every relabelling.**  Not about any particular law: the bound
holds at each ranking separately, which is what makes it a free lower bound over the WHOLE
design space rather than one certified at a chosen witness. -/
theorem even_rankSum (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0) (σ : Perm m) :
    2 / denom m ≤ ∑ k ∈ budgets m, regret (gFamily m) σ (denom m) k := by
  have hD : (0 : ℝ) < denom m := by unfold denom; positivity
  obtain ⟨j, hj, hj3⟩ := rankOf_has_heavy m (by omega) σ
  have h2 := even_total_excess (by omega) hmo (rankOf (gFamily m) σ)
    (ranked_even m hm hmo σ) j hj hj3
  rw [total_eq_sum_regret m (by omega) σ] at h2
  rw [div_le_iff₀ hD]
  nlinarith [h2]

/-- **`EvenEndpointData` needs only the endpoint law now.**  The third field is supplied, so
what remains for `even_frontier` is a single construction: a law band-feasible at `etaStar m`
whose objective reaches the free value.  Nothing here asserts that such a law exists. -/
def evenEndpointData_of_law (m : ℕ) (hm : 4 ≤ m) (hmo : m % 2 = 0)
    (P : Perm m → ℝ) (hband : P ∈ FeasibleAt id (etaStar m))
    (hvalue : objective m (by omega) P ≤ freeValue m) : EvenEndpointData m hm where
  endpoint := P
  endpoint_band := hband
  endpoint_value := hvalue
  rankSum := fun σ => even_rankSum m hm hmo σ

/-! ## Audit -/

#print axioms ranked_even
#print axioms even_rankSum

end CIGAMF.P13.PaperCEvenRankSum
