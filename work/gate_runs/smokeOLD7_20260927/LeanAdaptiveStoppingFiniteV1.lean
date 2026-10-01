import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Adaptive: a stopping time that MAY be infinite, shown finite from its tail.

## WHY THIS MODULE EXISTS

`LeanAdaptiveExpectedStoppingV1.expected_stopping_le` takes `tau : Omega -> N`.  Finiteness
of the stopping time is therefore a consequence of the TYPE and not of an argument: a run
that never stops has no representative in `N`, so it is silently outside the statement.  The
theorem is true and useful -- it converts a tail into an expectation -- but it cannot be
read as saying the scheme terminates, because termination was assumed by typing.

This module carries the honest object.  `tau : Omega -> N∞` admits a run that never stops,
and finiteness is DERIVED from the same geometric tail the expectation bound already
assumes.  Nothing new is assumed: the hypothesis

    mu {omega | n < tau omega} <= C * rho ^ n,   rho < 1, C finite

is exactly the one the original theorem takes, and it is shown to force

    mu {omega | tau omega = infinity} = 0.

The reading of the corpus changes accordingly.  What is proved about stopping is: given a
geometric tail, the time is almost surely finite AND its expectation is bounded.  What is
still assumed is the geometric tail itself, which belongs to the algorithm's own analysis
and is not supplied here.  That is a scope statement, and it is the accurate one.
-/

set_option maxHeartbeats 1000000

namespace CIGAMF.P13.AdaptiveStoppingFinite

open MeasureTheory ENNReal Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The event that the scheme has not stopped by time `n`, for a time that may be infinite. -/
def notYet (tau : Ω → ℕ∞) (n : ℕ) : Set Ω := {ω | (n : ℕ∞) < tau ω}

/-- The event that the scheme never stops. -/
def never (tau : Ω → ℕ∞) : Set Ω := {ω | tau ω = ⊤}

/-- Never stopping implies not having stopped by any finite time. -/
theorem never_subset_notYet (tau : Ω → ℕ∞) (n : ℕ) : never tau ⊆ notYet tau n := by
  intro ω hω
  simp only [never, Set.mem_setOf_eq] at hω
  simp only [notYet, Set.mem_setOf_eq, hω]
  exact lt_top_iff_ne_top.mpr (by simp)

/-- **A geometric tail forces almost-sure finiteness.**

This is the link the typed version got for free. The measure of never stopping is below
`C * rho ^ n` for every `n`, and a geometric sequence with ratio below one tends to zero, so
the measure is zero. -/
theorem never_measure_zero
    (μ : Measure Ω) (tau : Ω → ℕ∞) (C rho : ℝ≥0∞)
    (hC : C ≠ ⊤) (hrho : rho < 1)
    (htail : ∀ n : ℕ, μ (notYet tau n) ≤ C * rho ^ n) :
    μ (never tau) = 0 := by
  -- the measure of `never` is below every term of a sequence tending to zero
  have hle : ∀ n : ℕ, μ (never tau) ≤ C * rho ^ n := fun n =>
    le_trans (measure_mono (never_subset_notYet tau n)) (htail n)
  have hpow : Tendsto (fun n : ℕ => C * rho ^ n) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => rho ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hrho
    -- `const_mul` wants `b ≠ 0 ∨ a ≠ ⊤`; here the limit b IS zero, so the
    -- disjunct that holds is the second one, finiteness of the constant
    simpa using ENNReal.Tendsto.const_mul h0 (Or.inr hC)
  have hzero : μ (never tau) ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hpow hle
  exact nonpos_iff_eq_zero.mp hzero

/-- **The same statement, as the scope sentence the paper should carry.**

Given the geometric tail, the stopping time is finite almost everywhere. The tail itself is
an input: it is what the algorithm's own analysis must supply, and nothing here derives it. -/
theorem ae_finite_of_geometric_tail
    (μ : Measure Ω) (tau : Ω → ℕ∞) (C rho : ℝ≥0∞)
    (hC : C ≠ ⊤) (hrho : rho < 1)
    (htail : ∀ n : ℕ, μ (notYet tau n) ≤ C * rho ^ n) :
    ∀ᵐ ω ∂μ, tau ω ≠ ⊤ := by
  have h := never_measure_zero μ tau C rho hC hrho htail
  rw [ae_iff]
  simpa [never] using h

end CIGAMF.P13.AdaptiveStoppingFinite

#print axioms CIGAMF.P13.AdaptiveStoppingFinite.never_measure_zero
#print axioms CIGAMF.P13.AdaptiveStoppingFinite.ae_finite_of_geometric_tail
