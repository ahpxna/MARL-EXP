import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! Finite common-part inequality for a two-environment allocation decision.
This isolates the decision-theoretic step from the D6 regret-separation theorem.
Gaussian transcript comparison and its overlap integral remain separate. -/
namespace CIGAMF.P13.D6FiniteRiskLower
open scoped BigOperators
open Finset

/-- If every possible recommendation has total loss at least separation,
the sum of risks is bounded below by separation times the common mass. -/
theorem common_mass_risk_lower {Ω : Type*} (E : Finset Ω)
    (pminus pplus lossminus lossplus : Ω → ℝ) (separation : ℝ)
    (pm : ∀ x ∈ E, 0 ≤ pminus x) (pp : ∀ x ∈ E, 0 ≤ pplus x)
    (lm : ∀ x ∈ E, 0 ≤ lossminus x) (lp : ∀ x ∈ E, 0 ≤ lossplus x)
    (sep : ∀ x ∈ E, separation ≤ lossminus x+lossplus x) :
    separation*(∑ x ∈ E,min (pminus x) (pplus x)) ≤
      (∑ x ∈ E,pminus x*lossminus x)+(∑ x ∈ E,pplus x*lossplus x) := by
  rw [mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro x hx
  have hmin : 0 ≤ min (pminus x) (pplus x) := le_min (pm x hx) (pp x hx)
  have hs := mul_le_mul_of_nonneg_right (sep x hx) hmin
  have hm := mul_le_mul_of_nonneg_right (min_le_left (pminus x) (pplus x)) (lm x hx)
  have hp := mul_le_mul_of_nonneg_right (min_le_right (pminus x) (pplus x)) (lp x hx)
  nlinarith

/-- At least one of the two expected losses is at least half the common-part
bound. The distributions need not be normalized for this algebraic result. -/
theorem minimax_risk_lower {Ω : Type*} (E : Finset Ω)
    (pminus pplus lossminus lossplus : Ω → ℝ) (separation : ℝ)
    (pm : ∀ x ∈ E, 0 ≤ pminus x) (pp : ∀ x ∈ E, 0 ≤ pplus x)
    (lm : ∀ x ∈ E, 0 ≤ lossminus x) (lp : ∀ x ∈ E, 0 ≤ lossplus x)
    (sep : ∀ x ∈ E, separation ≤ lossminus x+lossplus x) :
    separation*(∑ x ∈ E,min (pminus x) (pplus x))/2 ≤
      max (∑ x ∈ E,pminus x*lossminus x) (∑ x ∈ E,pplus x*lossplus x) := by
  have hb := common_mass_risk_lower E pminus pplus lossminus lossplus separation pm pp lm lp sep
  have hm := le_max_left (∑ x ∈ E,pminus x*lossminus x) (∑ x ∈ E,pplus x*lossplus x)
  have hp := le_max_right (∑ x ∈ E,pminus x*lossminus x) (∑ x ∈ E,pplus x*lossplus x)
  linarith

#print axioms common_mass_risk_lower
#print axioms minimax_risk_lower
end CIGAMF.P13.D6FiniteRiskLower
