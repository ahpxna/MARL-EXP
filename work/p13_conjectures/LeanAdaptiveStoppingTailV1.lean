import Mathlib

/-! # Adaptive: the three probabilistic ingredients that were open.

`LeanAdaptiveConfidenceJoinV1` proves a statement ON the good event and nothing about
its probability, the tracking step, or the stopping time.  The audit (A5, A6) records
all three as open.  This file closes the parts that are theorems about the SCHEME --
the union bound, the tail-to-expectation step, and the overhead of a geometric grid --
and names precisely the one input that remains a concentration assumption.

## 1. `P(Eᶜ) ≤ δ` by peeling

The bad event is a countable union over arms and sample counts.  With the standard
budget `δ_{i,n} = δ/(K n(n+1))` the budgets sum to exactly `δ`, because
`∑_{n≥1} 1/(n(n+1)) = 1` telescopes.  So a per-`(i,n)` deviation bound of that size --
the ONE input that is a concentration inequality, not formalised here -- gives
`P(Eᶜ) ≤ δ`.

## 2. Stopping time: a geometric tail bounds the TAIL SUM

`P(τ > n) ≤ C ρ^n` with `ρ < 1` gives `∑_{n≥0} P(τ > n) ≤ C/(1-ρ)`.  That sum equals
`E[τ]` by the layer-cake identity, which is standard but is NOT re-proved here -- so
what this file bounds is the tail sum, and the step to `E[τ]` is cited, not proved.
High-probability correctness alone gives NOTHING here: off the good event the algorithm
may never stop, which is exactly why the tail is needed.

## 3. The doubling factor 4 is not sharp

A grid with ratio `1+ε` stops at the first target `≥ B*` and spends less than
`(1+ε)B* + b₀`.  So the overhead tends to `1` as `ε → 0`; the factor `4` of the
doubling schedule is an artefact of ratio `2`, not a property of the problem.

## WHAT IS PROVED

* `telescope_sum` — `∑_{n≥1} 1/(n(n+1)) = 1`.
* `peeling_budget` — the per-`(i,n)` budgets sum to `δ` over `K` arms.
* `union_bound` — `P(⋃ B_{i,n}) ≤ ∑ P(B_{i,n}) ≤ δ`, in a measure space.
* `geometric_tail_sum` — `∑_n C ρ^n = C/(1-ρ)` for `0 ≤ ρ < 1`.
* `expectation_of_tail` — a geometric tail bounds `∑_n P(τ > n)`.  The identity
  `E[τ] = ∑_n P(τ > n)` is the standard layer-cake fact and is CITED, not proved, so
  this is a bound on the tail sum and only thereby on `E[τ]`.
* `grid_overhead` — a ratio-`(1+ε)` grid spends less than `(1+ε)B* + b₀`, so the
  overhead is `1+ε`, not `4`.

## WHAT THIS DOES NOT ESTABLISH

- The per-`(i,n)` deviation bound itself.  That is a time-uniform concentration
  inequality for the GLR statistic, and it is an INPUT to `union_bound` here.
- The tracking step: that the empirical allocation converges to the oracle one.
- `E[τ] = ∑_{n≥0} P(τ > n)`: the identity is NOT proved.  Every statement here is
  about `∑_n P(τ > n)`.  Any sentence of the form "the expected stopping time is
  finite" is therefore one citation away from what is machine-checked.
-/

namespace CIGAMF.P13.AdaptiveStoppingTail

open Finset MeasureTheory
open scoped ENNReal NNReal

/-- The partial sums telescope: `∑_{n<N} 1/((n+1)(n+2)) = 1 - 1/(N+1)`. -/
theorem telescope_partial (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 : ℝ) / ((n + 1) * (n + 2)) = 1 - 1 / (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : ((N : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((N : ℝ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- …so they converge to `1`: the peeling budget is exactly exhausted. -/
theorem telescope_limit :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 : ℝ) / ((n + 1) * (n + 2)))
      Filter.atTop (nhds 1) := by
  have hfun : (fun N : ℕ => ∑ n ∈ Finset.range N, (1 : ℝ) / ((n + 1) * (n + 2)))
      = fun N : ℕ => 1 - 1 / ((N : ℝ) + 1) := funext telescope_partial
  rw [hfun]
  have hz : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using tendsto_const_nhds.sub hz

/-- The peeling budget over `K` arms: the partial sums reach exactly `delta`. -/
theorem peeling_budget (K : ℕ) (hK : 0 < K) (delta : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (K : ℝ) * (delta / ((K : ℝ) * ((n + 1) * (n + 2))))
      = delta * (1 - 1 / ((N : ℝ) + 1)) := by
  have hKne : (K : ℝ) ≠ 0 := by
    have : (0:ℝ) < (K : ℝ) := by exact_mod_cast hK
    exact ne_of_gt this
  have hrw : ∀ n : ℕ, (K : ℝ) * (delta / ((K : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) + 2))))
      = delta * ((1 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
    intro n
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    field_simp
  simp only [hrw]
  rw [← Finset.mul_sum, telescope_partial]

/-- The union bound, in a measure space: a countable family with summed budget `δ`. -/
theorem union_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : ℕ → Set Ω) (d : ℕ → ℝ≥0∞) (delta : ℝ≥0∞)
    (hB : ∀ n, μ (B n) ≤ d n) (hd : ∑' n, d n ≤ delta) :
    μ (⋃ n, B n) ≤ delta := by
  refine le_trans (measure_iUnion_le B) (le_trans (ENNReal.tsum_le_tsum hB) hd)

/-- A geometric tail sums to `C/(1-ρ)`. -/
theorem geometric_tail_sum (C rho : ℝ) (hC : 0 ≤ C) (h0 : 0 ≤ rho) (h1 : rho < 1) :
    ∑' n : ℕ, C * rho ^ n = C / (1 - rho) := by
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  ring

/-- **High probability is not enough**: a geometric tail is what bounds `∑_n P(τ > n)`,
hence the expected stopping time. -/
theorem expectation_of_tail (C rho : ℝ) (tail : ℕ → ℝ)
    (hC : 0 ≤ C) (h0 : 0 ≤ rho) (h1 : rho < 1)
    (hnn : ∀ n, 0 ≤ tail n) (hle : ∀ n, tail n ≤ C * rho ^ n)
    (hsum : Summable tail) :
    ∑' n : ℕ, tail n ≤ C / (1 - rho) := by
  have hgs : Summable (fun n : ℕ => C * rho ^ n) :=
    (summable_geometric_of_lt_one h0 h1).mul_left C
  refine le_trans (hsum.tsum_le_tsum hle hgs) ?_
  rw [geometric_tail_sum C rho hC h0 h1]

/-- **The factor 4 is an artefact of ratio 2.**  A ratio-`(1+ε)` grid stopping at the
first target `≥ B*` spends less than `(1+ε)B* + b₀`. -/
theorem grid_overhead (eps b0 Bstar target prev : ℝ)
    (heps : 0 < eps) (hb0 : 0 < b0) (hB : 0 < Bstar)
    (hprev : prev < Bstar) (hstep : target ≤ (1 + eps) * prev + b0) :
    target < (1 + eps) * Bstar + b0 := by
  have : (1 + eps) * prev < (1 + eps) * Bstar :=
    mul_lt_mul_of_pos_left hprev (by linarith)
  linarith

#print axioms telescope_partial
#print axioms telescope_limit
#print axioms peeling_budget
#print axioms union_bound
#print axioms geometric_tail_sum
#print axioms expectation_of_tail
#print axioms grid_overhead

end CIGAMF.P13.AdaptiveStoppingTail
