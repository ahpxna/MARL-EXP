import «LeanSupportObstructionQueryOrderV1»
import «LeanStructuralRandomMenuV1»

/-!
# Query/error tradeoff for the sparse and dense multi-tip families

The dense lower bound counts the worlds on which an arbitrary deterministic
adaptive tree can be correct.  The upper construction is represented by a
uniform `(b+1)`-subset of candidate worlds: query `b` members and use the last
as fallback.  Its per-world success probability is exactly `(b+1)/m`.
-/
namespace CIGAMF.P13.SupportQueryErrorTradeoff

open Finset
open CIGAMF.P13.SupportAdaptiveQuerySeparation
open CIGAMF.P13.SupportObstructionQueryOrder
open CIGAMF.P13.StructuralRandomMenu
noncomputable section
attribute [local instance] Classical.propDecidable
variable {m : ℕ}

def denseCorrect (t : Tree m) : Finset (Fin m) :=
  univ.filter (fun w => run (oracle w) t = w)

theorem dense_correct_subset (hm : 2 ≤ m) (t : Tree m) :
    denseCorrect t ⊆ insert (positiveOutput t) (positiveQueries t) := by
  intro w hw
  have hrun : run (oracle w) t = w := (mem_filter.mp hw).2
  by_cases hq : w ∈ positiveQueries t
  · exact mem_insert_of_mem hq
  · have hp := run_positive hm t w hq
    exact mem_insert.mpr (Or.inl (hrun.symm.trans hp))

/-- A depth-b deterministic adaptive tree is correct in at most `b+1` dense
worlds.  This is the Bayes counting lower bound under the uniform prior. -/
theorem dense_success_count (hm : 2 ≤ m) (t : Tree m) :
    (denseCorrect t).card ≤ depth t + 1 := by
  have hc := card_le_card (dense_correct_subset hm t)
  have hi := card_insert_le (positiveOutput t) (positiveQueries t)
  have hp := positive_card_le_depth t
  omega

theorem dense_error_count (hm : 2 ≤ m) (t : Tree m) :
    m - (depth t + 1) ≤ m - (denseCorrect t).card := by
  exact Nat.sub_le_sub_left (dense_success_count hm t) m

/-- Uniformly selecting `b+1` candidate worlds gives the exact per-world
success probability `(b+1)/m`; the candidate set is implemented by `b` queries
plus one fallback. -/
theorem uniform_dense_attainment (hm : 0 < m) (b : ℕ) (hb : b < m) (w : Fin m) :
    ((((univ : Finset (Fin m)).powersetCard (b+1)).filter
      (fun T => w ∈ T)).card : ℝ) /
        ((univ : Finset (Fin m)).powersetCard (b+1)).card = (b+1 : ℝ)/m := by
  have hw : w ∈ (univ : Finset (Fin m)) := mem_univ w
  have hK : 0 < b+1 := by omega
  have hKm : b+1 ≤ (univ : Finset (Fin m)).card := by simp; omega
  simpa using uniform_membership_probability (univ : Finset (Fin m)) w hw
    (b+1) hK hKm

/-- With no observations in the sparse family, the uniform random decision has
error exactly `1/m` in every world because only `j=w` is unsafe. -/
theorem sparse_zero_query_error_count (w : Fin m) :
    ((univ.filter (fun j : Fin m => j = w)).card : ℝ) = 1 := by
  have hfilter : univ.filter (fun j : Fin m => j = w) = {w} := by
    ext j
    simp
  rw [hfilter]
  simp

/-- One physical membership query is sufficient for zero sparse-family error;
this re-exports the geometric theorem in the error-tradeoff package. -/
theorem sparse_one_query_zero_error (hm : 2 ≤ m) (hm1 : 1 < m) (fallback : Fin m) :
    ∃ t : Tree m, depth t = 1 ∧ ∀ w : Fin m,
      CIGAMF.V4.SupportGeometry.selectedRadius
        (CIGAMF.P13.SupportMultiTipGeometry.components (sparseSup w))
        {run (CIGAMF.P13.SupportCardinalityQueryLaw.oracle (sparseSup w)) t} = 0 :=
  sparse_query_depth_attained hm hm1 fallback

#print axioms dense_correct_subset
#print axioms dense_success_count
#print axioms dense_error_count
#print axioms uniform_dense_attainment
#print axioms sparse_zero_query_error_count
#print axioms sparse_one_query_zero_error

end
end CIGAMF.P13.SupportQueryErrorTradeoff
