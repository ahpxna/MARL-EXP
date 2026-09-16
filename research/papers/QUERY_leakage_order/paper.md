# Which query you are allowed to ask sets the leakage order

**Draft — every mathematical claim below is machine-checked in Lean 4 unless the sentence
says otherwise. Theorem names in `monospace` are the formal statements; the module is
given in brackets.**

---

## Abstract

Two fixed worlds are to be told apart from observations. We hold the worlds fixed and
vary instead the *admissible measurement*. For a finite Gaussian mixture perturbed at
scale `h`, we show that the order `r` at which the two worlds first differ — the **leakage
order** — is a property of the query, not of the parameter space, and we compute what it
costs to restore distinguishability at that order.

The chain is closed end to end: the mixture's `h`-expansion is computed, the coefficients
below order `r` are shown to cancel, the order-`r` coefficient is shown **not** to vanish
identically, the squared Hellinger distance is sandwiched between two constant multiples
of `h^{2r}`, and the sandwich is converted into matching sample-complexity bounds and a
two-sided regret window.

---

## 1. What is new here, and what is not

*Ho and Nguyen, "Singularity structures and impacts on parameter estimation in finite
mixtures of distributions", arXiv:1609.02655.* Their Theorem 3.1 states that if `G₀` has
singularity level `r` relative to an ambient space `𝒢`, then

> $\inf_{G\in\mathcal G}\lVert p_G-p_{G_0}\rVert_\infty / W_s^s(G,G_0) > 0$ for any $s\ge r+1$,

with the analogue in total variation, and their Theorem 3.3(a) gives the minimax lower
bound $\inf_{\hat G_n}\sup_{G_0\in\mathcal G_r}\mathbb E\,W_s(\hat G_n,G_0)\gtrsim
n^{-1/(2s)}$ for `s ∈ [1, r+1)`, over a **compact** parameter space.

So **the phenomenon that singularity degrades the rate is prior, with minimax lower
bounds already proved**, as is the dependence on the singularity level through `r+1`.
This paper credits that and does not restate it as new.

What the prior does not contain, checked against the paper itself: the observation model
is **fixed throughout** — i.i.d. samples from the mixture density — and no theorem varies
which measurements are legal. No separation parameter `h` appears anywhere; rates are
powers of the sample size `n`. There is no cost of restoring distinguishability under a
restricted measurement class, and the subject is parameter estimation, not testing
between two fixed worlds.

**The claim of this paper** is therefore the measurement axis: the same two worlds acquire
*different* leakage orders under different admissible queries, and we price the restoration
of distinguishability at a given order. We do not claim the degradation phenomenon.

A note on a mis-statement in our own earlier project notes: it was recorded there that
"claiming only that the rate is `h^{-4}` puts the manuscript inside the prior". Read at
theorem level that is too strong — the prior contains no `h` at all. What it does contain
is the degradation phenomenon, and that is what must be credited.

---

## 2. Model and the object to be computed

The observation density of world `W` at perturbation `h` is the finite Gaussian mixture

$$p_{W,h}(y)=\sum_{x}\pi_x\,\varphi_\sigma\!\big(y-f_W(x)-h\,g(x)\big).$$

Expanding in `h` produces coefficients `Δ_j`, and the **leakage order** is the least `j`
with `Δ_j ≢ 0`. Two things must be established separately, and the second is the one
usually skipped:

1. the coefficients below order `r` cancel;
2. `Δ_r ≢ 0` — "some coefficient is nonzero" is *not* enough, because the shifted Gaussian
   derivatives could in principle cancel one another.

---

## 3. The expansion, computed rather than assumed

The Gaussian's iterated derivatives are built explicitly. `hpoly σ n` is the Hermite-type
sequence `H₀ = 1`, `H_{n+1} = H_n' − (y/σ²)H_n`.

**Theorem 3.1** (`iteratedDeriv_gauss` [`LeanQueryGaussianLevelV1`]).
`dⁿ/dyⁿ e^{−y²/2σ²} = H_n(y)·e^{−y²/2σ²}`.

**Theorem 3.2** (`hpoly_coeff`, `hpoly_ne_zero`, same module).
`H_n`'s degree-`n` coefficient is `(−1/σ²)ⁿ ≠ 0`, hence `H_n ≠ 0` — the fact the
non-vanishing argument needs.

**Theorem 3.3** (`iteratedDeriv_shift`, same module).
The `j`-th derivative in `h` at `h = 0` of one mixture component is `(−g)^j` times the
`j`-th Gaussian derivative. This is exactly where `g(x)^j`, and therefore the level
moment, comes from.

The step from one component to the whole mixture is a finite sum, and Mathlib has the
multilinear `iteratedFDeriv_fun_sum_apply` but no scalar-variable counterpart. We supply
it.

**Theorem 3.4** (`iteratedDeriv_fun_sum` [`LeanQueryMixtureDerivativeV1`]).
`iteratedDeriv` commutes with `Finset.sum` for functions that are `ContDiffAt` at the
point. Smoothness of each component is discharged by `contDiff_component`, not assumed.

**Theorem 3.5, the assembly** (`iteratedDeriv_mixture`, same module).
The `j`-th derivative in `h` at `h = 0` of the whole mixture equals the level sum of
order `j`, with level moment `M_j(v) = Σ_{x : f(x)=v} π_x(−g(x))^j`.

---

## 4. Cancellation below `r`, and non-vanishing at `r`

**Theorem 4.1, the easy half** (`mixture_coeff_diff_eq_zero`
[`LeanQueryMixtureDerivativeV1`]; `levelSum_eq_zero_of_levels_agree`
[`LeanQueryGaussianLevelV1`]).
Two worlds sharing a level set whose order-`j` level moments agree have the same order-`j`
coefficient.

**Theorem 4.2, the hard half** (`mixture_coeff_ne_zero`
[`LeanQueryMixtureDerivativeV1`]; `levelSum_ne_zero` [`LeanQueryGaussianLevelV1`]).
If the largest level carries a nonzero order-`r` moment, then `Δ_r` is somewhere nonzero.

The argument for 4.2 is worth stating because it is the step that makes the leakage order
well defined. Factor `φ_σ(y−v) = φ_σ(y)e^{vy/σ² − v²/2σ²}` and divide by the largest
level's factor. What remains is

$$T(y)=c_{v^\*}H_r(y-v^\*)+\sum_{v<v^\*}c_v H_r(y-v)\,e^{-(v^\*-v)y/\sigma^2+\text{const}},$$

in which every term of the second sum is a polynomial against a **decaying** exponential
and so tends to `0`. If `T ≡ 0`, the polynomial `c_{v*}H_r(·−v*)` would tend to `0` at
`+∞`, forcing its leading coefficient to vanish — contradicting `c_{v*} ≠ 0` and
`H_r ≠ 0` (Theorem 3.2). Hence the shifted Gaussian derivatives cannot conspire to
cancel.

---

## 5. The Hellinger sandwich

**Theorem 5.1, lower bound** (`hellinger_lower_from_interval`
[`LeanQueryHellingerIntervalV1`]).
If `|a_E|·h^r/2 ≤ t·H² + 2/t` for every `t > 0`, then

$$H^2 \;\ge\; \frac{a_E^2\,h^{2r}}{32}.$$

The constant is `32`, not `16`; it comes from the Cauchy–Schwarz interval bound
(`sq_le_of_all_t`, `gap_le_of_integrals`) and we flag it because the looser constant is
easy to write by accident.

**Theorem 5.2, upper bound** (`hellinger_upper_const` [`LeanQueryTaylorRemainderV1`]).
With an integrable envelope `G` satisfying `|p_A − p_B| ≤ h^r·G` pointwise and
`∫ G²/p_B = J`,

$$H^2 \;=\; \tfrac12\!\int(\sqrt{p_A}-\sqrt{p_B})^2 \;\le\; \tfrac{J}{2}\,h^{2r}.$$

The ingredients are proved, not assumed: `chi2_pointwise` bounds the Hellinger integrand
by the `χ²` integrand; `bound_of_vanishing_derivs` is the uniform Taylor remainder;
`gauss_lower_envelope`, `gauss_upper_envelope`, `majorise` and `envelope_integrable` build
the integrable Gaussian envelope; `gaussComp_contDiff` supplies the smoothness.

So `H² ≍ h^{2r}`, with both constants explicit.

---

## 6. Sample complexity, matching on both sides

**Theorem 6.1** (`log_sandwich` [`LeanQuerySampleComplexityV1`]).
For `0 ≤ H² ≤ 1/2`, `H² ≤ −log(1−H²) ≤ 2H²`. This converts the Hellinger sandwich into a
sandwich on the per-sample log-affinity `L = −log(1−H²)`.

**Theorem 6.2** (`matching_rate`, same module).
If `c₋h^{2r} ≤ H² ≤ c₊h^{2r}` then `c₋h^{2r} ≤ L ≤ 2c₊h^{2r}`, and the sufficiency
condition transfers.

**Theorem 6.3, sufficiency** (`sufficient_count`, same module).
If `log(1/(2ε)) ≤ N·L` with `L = −log ρ`, then `ρ^N/2 ≤ ε`.

**Theorem 6.4, necessity and rounding** (`necessary_count`, `ceil_suffices`, same module).
The matching lower bound, and the statement that the integer ceiling suffices.

The two sides differ by the factor `2` of Theorem 6.1 and the ratio `c₊/c₋` of §5 —
both explicit, neither hidden in an asymptotic.

---

## 7. From distinguishability to regret

**Theorem 7.1** (`outside_cost`, `inside_cost`, `regret_ge_gamma_error`
[`LeanQueryRegretBridgeV1`]).
The decision cost decomposes so that regret is bounded below by `γ` times the error
probability.

**Theorem 7.2** (`lrt_regret_le`, same module).
The likelihood-ratio test's regret is bounded above by `L_max` times the error
probability.

**Theorem 7.3, the window** (`bayes_regret_window`, same module).
If `ρ^{2N}/4 ≤ e ≤ ρ^N/2` and `γ·e ≤ R ≤ L_max·e`, then

$$\frac{\gamma\,\rho^{2N}}{4}\;\le\;R\;\le\;\frac{L_{\max}\,\rho^{N}}{2}.$$

With the project's constants `γ = 13983/32768` and `L_max = 2401/4096`, measured regret
on two instances was `0.00835` and `0.00916`, both inside the window (artifact `P33`).
That is a numerical check of a proved inequality, not evidence for it.

---

## 8. Formal verification

Lean 4, toolchain `leanprover/lean4:v4.34.0-rc2`, mathlib rev
`1f495c611d05d2215058cd77c7897d625bc3b445`. Acceptance per module requires
`lean_exit = 0`, zero errors, source hash unchanged across the compile, `.olean` newer
than source, at least one `#print axioms`, and axioms contained in
`{propext, Classical.choice, Quot.sound}`. No module contains `sorry`.

| Module | Audited names | Accepted |
|---|---|---|
| `LeanQueryGaussianLevelV1` | 13 | yes |
| `LeanQueryMixtureDerivativeV1` | 5 | yes |
| `LeanQueryHellingerIntervalV1` | 7 | yes |
| `LeanQueryHellingerEnvelopeV1` | 9 | yes |
| `LeanQueryTaylorRemainderV1` | 7 | yes |
| `LeanQuerySampleComplexityV1` | 8 | yes |
| `LeanQueryRegretBridgeV1` | 5 | yes |

---

## 9. Scope, and what is not established

1. **Normalising constants are dropped.** The factor `1/(σ√(2π))` and the `1/j!` of the
   Taylor expansion are positive constants, dropped throughout because they change no
   vanishing statement. The manuscript must not quote the dropped expressions as
   densities.
2. **`mixture_coeff_diff_eq_zero` assumes a shared level set.** Worlds with different
   level sets are not covered by that statement.
3. **The non-vanishing argument needs a strict top level.** `levelSum_ne_zero` requires a
   unique largest level carrying a nonzero coefficient; ties at the top are outside it.
4. **The regret window is two-sided but not tight.** The ratio between its ends is
   `2L_max ρ^{-N}/γ`, which grows with `N`. It localises the regret; it does not determine
   it.
5. **No minimax statement.** Everything here is about two fixed worlds under a fixed
   admissible query. No infimum over estimators or over decision rules is taken, so
   nothing here is a minimax theorem, and the comparison with Ho–Nguyen's minimax lower
   bounds is a comparison of *different objects*.

---

## 10. Open

* A characterisation of which query classes induce which leakage orders, rather than the
  present per-instance computation.
* Tightening §7's window, whose ends separate as `N` grows.
* Whether the constant `32` of Theorem 5.1 is attained, or is an artefact of the interval
  bound.
