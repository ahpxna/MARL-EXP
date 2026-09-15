import Mathlib.Probability.Decision.Risk.Basic
import Mathlib.Probability.Decision.Risk.Countable

/-! # The equaliser-prior bridge to `ProbabilityTheory.minimaxRisk`

The D6 same-response chain proves its lower bound by exhibiting a prior against
which EVERY finite randomized rule has the same expected regret
(`randomized_dual_equalizer`).  That is exactly a Bayes-risk statement, and
Mathlib's decision-theoretic layer already carries the principle that a Bayes
risk lower-bounds the minimax risk.  This file isolates the two hinges so the
chain's results can be stated in the standard vocabulary rather than an ad hoc
one, and so the same scaffold serves the discovery lower bound.

Nothing here is specific to D6.  Both statements are three-line consequences of
`bayesRisk_le_minimaxRisk` and `iInf₂_le_of_le`; their value is that they name
the exact obligation each half of a minimax proof must discharge:

* lower: produce ONE prior and a bound valid against EVERY Markov kernel;
* upper: produce ONE Markov kernel and a bound valid at EVERY parameter.
-/
namespace CIGAMF.MinimaxRiskBridge
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨}

/-- An equalising prior certifies a minimax lower bound.  The hypothesis is the
shape `randomized_dual_equalizer` delivers: a single prior `π` against which the
average risk of every Markov kernel is at least `v`. -/
theorem minimaxRisk_ge_of_equalizer (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [IsProbabilityMeasure π] (v : ℝ≥0∞)
    (h : ∀ κ : Kernel 𝓧 𝓨, IsMarkovKernel κ → v ≤ avgRisk ℓ P κ π) :
    v ≤ minimaxRisk ℓ P :=
  le_trans (le_iInf₂ h) (bayesRisk_le_minimaxRisk ℓ P π)

/-- One strategy with a uniform per-parameter bound certifies a minimax upper
bound.  This is the shape `actual_two_action_risk` delivers: a fixed randomized
rule whose risk is at most `v` in EVERY world, not merely in the worst one. -/
theorem minimaxRisk_le_of_strategy (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (κ : Kernel 𝓧 𝓨) (hκ : IsMarkovKernel κ) (v : ℝ≥0∞)
    (h : ∀ θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) ≤ v) :
    minimaxRisk ℓ P ≤ v :=
  iInf₂_le_of_le κ hκ (iSup_le h)

/-- Both halves meet: the minimax risk is exactly `v`. -/
theorem minimaxRisk_eq_of_equalizer_and_strategy (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [IsProbabilityMeasure π] (κ : Kernel 𝓧 𝓨) (hκ : IsMarkovKernel κ)
    (v : ℝ≥0∞)
    (hlow : ∀ κ' : Kernel 𝓧 𝓨, IsMarkovKernel κ' → v ≤ avgRisk ℓ P κ' π)
    (hup : ∀ θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) ≤ v) :
    minimaxRisk ℓ P = v :=
  le_antisymm (minimaxRisk_le_of_strategy ℓ P κ hκ v hup)
    (minimaxRisk_ge_of_equalizer ℓ P π v hlow)

/-- Finite parameter set: the equaliser hypothesis in the summation form the D6
certificates actually produce. -/
theorem minimaxRisk_ge_of_equalizer_fintype [Fintype Θ] [MeasurableSingletonClass Θ]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (π : Measure Θ) [IsProbabilityMeasure π]
    (v : ℝ≥0∞)
    (h : ∀ κ : Kernel 𝓧 𝓨, IsMarkovKernel κ →
      v ≤ ∑ θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ))*π {θ}) :
    v ≤ minimaxRisk ℓ P := by
  refine minimaxRisk_ge_of_equalizer ℓ P π v (fun κ hκ => ?_)
  rw [avgRisk_fintype]
  exact h κ hκ

#print axioms minimaxRisk_ge_of_equalizer
#print axioms minimaxRisk_le_of_strategy
#print axioms minimaxRisk_eq_of_equalizer_and_strategy
#print axioms minimaxRisk_ge_of_equalizer_fintype

end CIGAMF.MinimaxRiskBridge
