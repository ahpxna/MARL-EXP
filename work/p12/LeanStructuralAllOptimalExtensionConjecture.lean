import Mathlib
import «LeanStructuralRankabilityCharacterizationV1»

/-! QUARANTINED / COUNTEREXAMPLE FOUND.

The former shell treated nested regret and extension defect as unrelated
nonnegative reals.  Those premises cannot imply the proposed scaled bound:
take regret `1` and defect `0`.  A future theorem must first introduce the
actual finite structural definitions and prove their missing relationship.
-/
namespace CIGAMF.P13.StructuralApprox

/-- Exact counterexample to the old placeholder premises.  This does not
falsify a future statement over correctly connected finite definitions; it
only kills the disconnected-real shell. -/
theorem disconnected_scaled_shell_is_false :
    ¬ (∀ bestNestedChainRegret allOptimalExtensionDefect : ℝ,
      0 ≤ bestNestedChainRegret →
      0 ≤ allOptimalExtensionDefect →
      bestNestedChainRegret ≤
        (Fintype.card Unit : ℝ) * allOptimalExtensionDefect) := by
  intro h
  have hbad := h 1 0 (by norm_num) (by norm_num)
  norm_num at hbad

end CIGAMF.P13.StructuralApprox
