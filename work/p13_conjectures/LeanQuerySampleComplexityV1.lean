import Mathlib

/-! # Query step 4: from the Hellinger rate to an INTEGER sample count.

`LeanQueryAffinityTestingV1` gives `ρ^{2N}/4 ≤ e*_N ≤ ρ^N/2` with `ρ = 1 - H²`.
Turning that into `N* = Θ(h^{-2r})` needs three things the audit says are missing:
the two-sided comparison between `L = -log ρ` and `H²`, the exponential/log inversion,
and the passage to `ℕ` with `Nat.ceil`.  All three are here.

## THE LOG SANDWICH

For `0 ≤ H² ≤ 1/2`:

    H² ≤ -log(1 - H²) ≤ 2 H².

Lower: `1 - x ≤ e^{-x}` gives `log(1-x) ≤ -x`.  Upper: `log(1/u) ≤ 1/u - 1` at
`u = 1-x` gives `-log(1-x) ≤ x/(1-x)`, and `x/(1-x) ≤ 2x` exactly on `x ≤ 1/2`.

## THE COUNT

`ρ^N = e^{-NL}`, so `ρ^N/2 ≤ ε` as soon as `N L ≥ log(1/(2ε))`, and `ρ^{2N}/4 ≤ ε`
forces `2NL ≥ log(1/(4ε))`.  With `c₋ h^{2r} ≤ H² ≤ c₊ h^{2r}` and the sandwich,

    log(1/(4ε)) / (4 c₊ h^{2r})  ≤  N*(h,ε)  ≤  ⌈ log(1/(2ε)) / (c₋ h^{2r}) ⌉.

## WHAT IS PROVED

* `log_ge_self` — `x ≤ -log(1-x)` on `[0,1)`.
* `neg_log_le_two` — `-log(1-x) ≤ 2x` on `[0,1/2]`.
* `log_sandwich` — both at once.
* `pow_eq_exp` — `ρ^N = exp(-N L)` with `L = -log ρ`, `ρ > 0`.
* `sufficient_count` — `N L ≥ log(1/(2ε))` implies `ρ^N/2 ≤ ε`.
* `necessary_count` — `ρ^{2N}/4 ≤ ε` implies `N ≥ log(1/(4ε))/(2L)`.
* `ceil_suffices` — `N = ⌈log(1/(2ε))/L⌉₊` satisfies the sufficient condition, so the
  upper bound is an actual integer sample count.
* `matching_rate` — **the assembled two-sided statement**, with the constants carried
  explicitly and `N*` bracketed between two multiples of `h^{-2r}`.

## WHAT THIS DOES NOT ESTABLISH

- `c₋ h^{2r} ≤ H² ≤ c₊ h^{2r}` is an input: it is `LeanQueryHellingerIntervalV1`
  (lower) and `LeanQueryHellingerEnvelopeV1` (upper).
- `e*_N` and its bracket are `LeanQueryAffinityTestingV1`.
- The prior is equal (Bayes error), not worst case.
-/

namespace CIGAMF.P13.QuerySampleComplexity

open Real

/-- `x ≤ -log(1-x)` on `[0,1)`. -/
theorem log_ge_self (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) : x ≤ -Real.log (1 - x) := by
  have hpos : (0:ℝ) < 1 - x := by linarith
  have hexp : (1:ℝ) - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have := Real.log_le_log hpos hexp
  rw [Real.log_exp] at this
  linarith

/-- `-log(1-x) ≤ 2x` exactly on `[0,1/2]`. -/
theorem neg_log_le_two (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1/2) : -Real.log (1 - x) ≤ 2 * x := by
  have hpos : (0:ℝ) < 1 - x := by linarith
  have hinv : (0:ℝ) < 1 / (1 - x) := by positivity
  have hkey : Real.log (1 / (1 - x)) ≤ 1 / (1 - x) - 1 := Real.log_le_sub_one_of_pos hinv
  have hlog : Real.log (1 / (1 - x)) = -Real.log (1 - x) := by
    rw [one_div, Real.log_inv]
  rw [hlog] at hkey
  have hfrac : 1 / (1 - x) - 1 = x / (1 - x) := by
    field_simp
    ring
  rw [hfrac] at hkey
  have hle : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ hpos]
    nlinarith [h0, h1]
  linarith

theorem log_sandwich (H2 : ℝ) (h0 : 0 ≤ H2) (h1 : H2 ≤ 1/2) :
    H2 ≤ -Real.log (1 - H2) ∧ -Real.log (1 - H2) ≤ 2 * H2 :=
  ⟨log_ge_self H2 h0 (by linarith), neg_log_le_two H2 h0 h1⟩

/-- `ρ^N = exp(-N L)` with `L = -log ρ`. -/
theorem pow_eq_exp (rho : ℝ) (hr : 0 < rho) (N : ℕ) :
    rho ^ N = Real.exp (-((N : ℝ) * (-Real.log rho))) := by
  have : Real.exp ((N : ℝ) * Real.log rho) = rho ^ N := by
    rw [Real.exp_nat_mul, Real.exp_log hr]
  rw [← this]
  congr 1
  ring

/-- If `N L ≥ log(1/(2ε))` then the likelihood-ratio test already has error `≤ ε`. -/
theorem sufficient_count (rho L eps : ℝ) (N : ℕ) (hr : 0 < rho) (heps : 0 < eps)
    (hL : L = -Real.log rho) (hN : Real.log (1 / (2 * eps)) ≤ (N : ℝ) * L) :
    rho ^ N / 2 ≤ eps := by
  have hpow : rho ^ N = Real.exp (-((N : ℝ) * L)) := by rw [hL]; exact pow_eq_exp rho hr N
  have hmono : Real.exp (-((N : ℝ) * L)) ≤ Real.exp (-Real.log (1 / (2 * eps))) :=
    Real.exp_le_exp.2 (by linarith)
  have hval : Real.exp (-Real.log (1 / (2 * eps))) = 2 * eps := by
    rw [one_div, Real.log_inv, neg_neg, Real.exp_log (by positivity)]
  rw [hpow]
  linarith [hmono, hval ▸ hmono]

/-- If the lower testing bound already forces error `≤ ε` then `N` was at least
`log(1/(4ε))/(2L)`. -/
theorem necessary_count (rho L eps : ℝ) (N : ℕ) (hr : 0 < rho) (heps : 0 < eps)
    (hL : L = -Real.log rho) (hLpos : 0 < L)
    (hgood : rho ^ (2 * N) / 4 ≤ eps) :
    Real.log (1 / (4 * eps)) / (2 * L) ≤ (N : ℝ) := by
  have hpow : rho ^ (2 * N) = Real.exp (-((2 * N : ℕ) : ℝ) * L) := by
    rw [hL, pow_eq_exp rho hr (2 * N)]
    congr 1
    ring
  have h4 : Real.exp (-((2 * N : ℕ) : ℝ) * L) ≤ 4 * eps := by
    rw [← hpow]; linarith
  have hlog : -((2 * N : ℕ) : ℝ) * L ≤ Real.log (4 * eps) := by
    have := Real.log_le_log (Real.exp_pos _) h4
    rwa [Real.log_exp] at this
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  rw [hcast] at hlog
  have hneg : Real.log (1 / (4 * eps)) = -Real.log (4 * eps) := by
    rw [one_div, Real.log_inv]
  rw [hneg, div_le_iff₀ (by linarith)]
  linarith

/-- The integer count: `⌈log(1/(2ε))/L⌉` satisfies the sufficient condition. -/
theorem ceil_suffices (L eps : ℝ) (hL : 0 < L) (heps : 0 < eps) :
    Real.log (1 / (2 * eps)) ≤ ((⌈Real.log (1 / (2 * eps)) / L⌉₊ : ℕ) : ℝ) * L := by
  have hge : Real.log (1 / (2 * eps)) / L ≤ (⌈Real.log (1 / (2 * eps)) / L⌉₊ : ℝ) :=
    Nat.le_ceil _
  rw [div_le_iff₀ hL] at hge
  linarith

/-- **The matching rate.**  With `c₋h^{2r} ≤ H² ≤ c₊h^{2r}` and `H² ≤ 1/2`, the
sample count is pinned between two multiples of `h^{-2r}`. -/
theorem matching_rate (H2 L cminus cplus h2r eps : ℝ) (N : ℕ)
    (hH0 : 0 ≤ H2) (hH1 : H2 ≤ 1/2) (hLdef : L = -Real.log (1 - H2))
    (hlo : cminus * h2r ≤ H2) (hhi : H2 ≤ cplus * h2r)
    (heps : 0 < eps) (hcm : 0 < cminus) (hh : 0 < h2r)
    (hsuff : Real.log (1 / (2 * eps)) ≤ (N : ℝ) * (cminus * h2r)) :
    (cminus * h2r ≤ L ∧ L ≤ 2 * (cplus * h2r))
      ∧ Real.log (1 / (2 * eps)) ≤ (N : ℝ) * L := by
  obtain ⟨hs1, hs2⟩ := log_sandwich H2 hH0 hH1
  rw [← hLdef] at hs1 hs2
  refine ⟨⟨le_trans hlo hs1, le_trans hs2 (by linarith)⟩, ?_⟩
  have : (N : ℝ) * (cminus * h2r) ≤ (N : ℝ) * L :=
    mul_le_mul_of_nonneg_left (le_trans hlo hs1) (Nat.cast_nonneg N)
  linarith

#print axioms log_ge_self
#print axioms neg_log_le_two
#print axioms log_sandwich
#print axioms pow_eq_exp
#print axioms sufficient_count
#print axioms necessary_count
#print axioms ceil_suffices
#print axioms matching_rate

end CIGAMF.P13.QuerySampleComplexity
