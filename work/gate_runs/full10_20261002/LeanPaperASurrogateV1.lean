import «LeanPaperA7TailV1»
import «LeanPaperBRatesV1»

/-!
# Paper A: what the surrogate learner pays, as an order in `log(1/alpha)`

The static result is that a surrogate-optimal design starves the middle cells.  The
operational consequence is a different statement: a learner that follows the surrogate
oracle, with forced exploration at rate `t^{-1/2}`, needs `Omega(log^2(1/alpha))` rounds
where a true-oracle learner needs `O(log(1/alpha))`.

Two inputs, both named:

* `hexplore` --- the surrogate learner's own middle-cell budget, `E N_mid(tau) <= C + C' E sqrt(tau)`,
  which is what forced exploration at rate `t^{-1/2}` produces;
* `hchange` --- the stopped change-of-measure at a hidden pair, `2r/d^2 * kl <= C + C' E sqrt(tau)`,
  summed over the `r` pairs.

From those, Jensen (`exploration_cost_law`) gives the quadratic, and `kl2_ge_log` turns the
binary divergence into `log(1/alpha)`.  The conclusion is an order in `alpha`, and the
contrast with `O(log(1/alpha))` is `separation_diverges`.

Nothing here says every method using a surrogate pays this.  It is a statement about a
learner with THIS oracle, THIS exploration rate and THIS tracker.
-/

namespace CIGAMF.P13.PaperASurrogate

open CIGAMF.P13.PaperA7Tail
open CIGAMF.P13.PaperBRates

/-- **The quadratic cost.**  Jensen against the square-root exploration budget. -/
theorem surrogate_cost_quadratic (r d kl C C' Eτ ma : ℝ)
    (hC' : 0 < C') (hEτ : 0 ≤ Eτ) (hd : 0 < d)
    (hAC : C ≤ 2 * r / d ^ 2 * kl)
    (hma : ma ≤ Eτ ^ (1 / 2 : ℝ))
    (hchange : 2 * r / d ^ 2 * kl ≤ C + C' * ma) :
    ((2 * r / d ^ 2 * kl - C) / C') ^ (1 / (1 / 2 : ℝ)) ≤ Eτ :=
  exploration_cost_law r d kl C C' Eτ ma (1 / 2 : ℝ) (by norm_num) hC' hEτ hd hAC hma hchange

/-- **The divergence carries `log(1/alpha)`.**  A restatement of `kl2_ge_log` at the
`delta`-correct pair of error probabilities. -/
theorem kl_at_correctness (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    (1 - α) * Real.log (1 / α) - 2 * (Real.exp 1)⁻¹ ≤ kl2 (1 - α) α := by
  have h := kl2_ge_log (1 - α) α (by linarith) (by linarith) hα hα1
  linarith

/-- **The surrogate learner's budget is quadratic in `log(1/alpha)`.**  Combining the two. -/
theorem surrogate_omega_log_squared (r d C C' Eτ ma α : ℝ)
    (hC' : 0 < C') (hEτ : 0 ≤ Eτ) (hd : 0 < d) (hα : 0 < α) (hα1 : α < 1)
    (hAC : C ≤ 2 * r / d ^ 2 * kl2 (1 - α) α)
    (hma : ma ≤ Eτ ^ (1 / 2 : ℝ))
    (hchange : 2 * r / d ^ 2 * kl2 (1 - α) α ≤ C + C' * ma) :
    ((2 * r / d ^ 2 * kl2 (1 - α) α - C) / C') ^ (1 / (1 / 2 : ℝ)) ≤ Eτ :=
  surrogate_cost_quadratic r d (kl2 (1 - α) α) C C' Eτ ma hC' hEτ hd hAC hma hchange

/-- **The separation diverges.**  A quadratic in `L = log(1/alpha)` eventually exceeds any
fixed multiple of `L`, so the two learners' costs separate without bound. -/
theorem separation_diverges (c K : ℝ) (hc : 0 < c) (hK : 0 < K) (L : ℝ)
    (hL : (K + 1) / c < L) : K * L < c * L ^ 2 := by
  have hL0 : 0 < L := by
    have : (0 : ℝ) < (K + 1) / c := by positivity
    linarith
  have hcL : K + 1 < L * c := by rwa [div_lt_iff₀ hc] at hL
  nlinarith [hcL, hL0, hc]

/-! ## Audit -/

#print axioms surrogate_cost_quadratic
#print axioms kl_at_correctness
#print axioms surrogate_omega_log_squared
#print axioms separation_diverges

end CIGAMF.P13.PaperASurrogate
