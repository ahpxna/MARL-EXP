import Mathlib

/-! # Query: from `c_- h^{2r} ≤ H² ≤ c_+ h^{2r}` to a two-sided sample complexity.

`scripts/P15_query_hellinger_order.py` supplies the two constants on the real finite
Gaussian mixture, by the interval route: the dominating level `v*` is exhibited and
the tail domination checked (the ratio to the leading term reaches `1.000000000` at
`y = v* + 640`), an interval `E` on which `Δ_r` keeps its sign gives
`a_E = ∫_E Δ_r`, and then

    order 2 (g₀):  c_- = a_E²/16 = 9.056e-07,   c_+ = 2.527e-05
    order 1 (u):   c_- = 7.171e-07,             c_+ = 5.001e-05.

`scripts/P9_query_transcript_complexity.py` supplies the transcript half: the
affinity tensorises and the equal-prior Bayes error obeys
`(1/4)ρ^{2N} ≤ e*_N ≤ (1/2)ρ^N`, validated against a Gaussian pair with a closed-form
N-sample error.  What is left is the arithmetic that turns those into a rate, and
that arithmetic is what this file proves -- so the open part of the Query chain is
exactly the two analytic constants, not the assembly.

## WHAT IS PROVED

* `log_ge_self` — `H² ≤ -log(1 - H²)` for `0 ≤ H² < 1`.  One direction is free from
  `log x ≤ x - 1`.
* `necessary_bound` / `sufficient_bound` — inverting the testing bracket: to reach
  error `ε` one NEEDS at least `log(1/(4ε))/(2L)` observations and `⌈log(1/(2ε))/L⌉`
  SUFFICE, with `L = -log ρ`.
* `rate_two_sided` — substituting `H² ≤ L ≤ 2H²` and `c_- h^{2r} ≤ H² ≤ c_+ h^{2r}`:

      log(1/(4ε)) / (4 c_+ h^{2r})  ≤  N_necessary  and
      N_sufficient  ≤  log(1/(2ε)) / (c_- h^{2r}),

  so both ends are `Θ(h^{-2r})` and the spread is the constant `c_+/c_-` times a
  factor depending only on `ε`.

## WHAT THIS DOES NOT ESTABLISH

- `L ≤ 2H²` for `H² ≤ 1/2` is taken as a HYPOTHESIS here (`hLup`); only the other
  direction is proved.  It is elementary and the script checks it numerically.
- The constants `c_±` are measured, not proved: the Taylor remainder bounds of steps
  3b and 3c are verified on a grid of `h`, not formalised.
- `e*_N`'s bracket is `LeanQueryAffinityTestingV1`; nothing here re-proves it.
-/

namespace CIGAMF.P13.QueryRateAssembly

noncomputable section

open Real

/-- The free direction: `H² ≤ -log(1 - H²)`. -/
theorem log_ge_self (H2 : ℝ) (h0 : 0 ≤ H2) (h1 : H2 < 1) :
    H2 ≤ -Real.log (1 - H2) := by
  have hpos : 0 < 1 - H2 := by linarith
  have := Real.log_le_sub_one_of_pos hpos
  linarith

/-- Inverting the lower testing bound: fewer than this many observations cannot
reach error `ε`. -/
theorem necessary_bound (L eps N : ℝ) (hL : 0 < L) (heps : 0 < eps)
    (hbound : Real.log (1/(4*eps)) ≤ 2*L*N) :
    Real.log (1/(4*eps))/(2*L) ≤ N := by
  rw [div_le_iff₀ (by linarith : (0:ℝ) < 2*L)]
  linarith

/-- And the upper: this many suffice. -/
theorem sufficient_bound (L eps N : ℝ) (hL : 0 < L) (heps : 0 < eps)
    (hN : Real.log (1/(2*eps))/L ≤ N) :
    Real.log (1/(2*eps)) ≤ L*N := by
  rw [div_le_iff₀ hL] at hN
  linarith

/-- THE RATE.  Both ends are `Theta(h^{-2r})`. -/
theorem rate_two_sided (H2 L cminus cplus h2r eps : ℝ)
    (hcm : 0 < cminus) (hcp : 0 < cplus) (hh : 0 < h2r) (heps : 0 < eps)
    (hlo : cminus * h2r ≤ H2) (hhi : H2 ≤ cplus * h2r)
    (hLlo : H2 ≤ L) (hLup : L ≤ 2*H2)
    (hlog4 : 0 ≤ Real.log (1/(4*eps))) (hlog2 : 0 ≤ Real.log (1/(2*eps))) :
    Real.log (1/(4*eps))/(4*cplus*h2r) ≤ Real.log (1/(4*eps))/(2*L)
    ∧ Real.log (1/(2*eps))/L ≤ Real.log (1/(2*eps))/(cminus*h2r) := by
  have hH2pos : 0 < H2 := lt_of_lt_of_le (mul_pos hcm hh) hlo
  have hLpos : 0 < L := lt_of_lt_of_le hH2pos hLlo
  constructor
  · refine div_le_div_of_nonneg_left hlog4 (by linarith) ?_
    calc 2*L ≤ 2*(2*H2) := by linarith
      _ ≤ 4*(cplus*h2r) := by linarith
      _ = 4*cplus*h2r := by ring
  · exact div_le_div_of_nonneg_left hlog2 (mul_pos hcm hh) (le_trans hlo hLlo)

#print axioms log_ge_self
#print axioms necessary_bound
#print axioms sufficient_bound
#print axioms rate_two_sided

end
end CIGAMF.P13.QueryRateAssembly
