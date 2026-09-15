# Batch R — single acceptance pass

## Second pass: 20 modules, 106 clean audits, 0 failures

Four modules added after the first pass, all `accepted=True`, `nonstandard=0`:

| module | audits | closes |
|---|---:|---|
| `LeanFunctionalContrastDualityV1` | 4 | **R1 duality** |
| `LeanD6ScalarOptimalAssemblyV1` | 2 | **R2 assembly** |
| `LeanSupportPassiveSamplingMassV1` | 18 | **R4 probability layer** |
| `LeanSupportParityBundleSizeV1` | 14 | **R5 bundle size** |

**R1 duality.** A harmonic potential `p` (`L p = e_a - e_b`) induces the flow
`f i j = c i j * (p i - p j)`. `induced_unitFlow` shows it is a unit flow,
`harmonic_energy` that `2 * contrastEnergy c p = p a - p b`, and
`induced_flowResistance` that `flowResistance c f = p a - p b`. So the potential
certificate gives `delta^2*(R/2)/R^2` and the flow certificate `delta^2/(2R)` —
the same number. `pair_infimum_exact` concludes the pair-restricted infimum is
exactly `delta^2/(2R)`, attained. No LP duality theorem and no pseudoinverse are
used. STILL ASSUMED: existence of the harmonic potential (the one remaining
solve), and the result is per pair — the minimisation over pairs is not here.

**R2 assembly.** `exists_swap_capping_design`: for every legal cost-normalised
design there EXISTS an adjacent swap alternative against which it collects at
most `mu^2/(2q)` per unit cost. Averaging, not optimisation: the per-measurement
mixture bound (`measurement_mixture_bound`, both constructors) times `w e/charge e`,
summed and with the two finite sums exchanged, caps the total over the `q(q+1)`
swaps; a sum of `q(q+1)` terms bounded by `q(q+1)*V` has a term at most `V`. With
`uniform_B_lower` this is the "hence the scalar design is optimal" step that was
prose. STILL OPEN: the alternative is an adjacent swap at the true margin, so
this is the upper half only; the converse is not proved.

**R4 probability layer.** `LeanSupportPassiveSamplingMassV1` supplies the real
measure-theoretic model — `Measure.pi` over `PMF (Points W)`, i.e. genuine i.i.d.
draws from the actual support — and `miss_probability` is an EQUALITY,
`iid W p N (missed W w N) = (1 - p (some w))^N`, not a bound. Union bound then
`sample_size_suffices` gives `passive_certified_safe_whp`. `gamma_zero_vacuous`
confirms the mass hypothesis is load-bearing, so the negative theorem stands.

**R5 bundle size.** Headline is NOT parity. Under one membership primitive the
bundle size is set by how the danger region sits relative to the query class:
multi-tip 1 (proved), interval and laminar 1 (numerical), parity exactly `d`
(proved, via a fully adaptive pairing `adaptive_balanced` whose involution is
transcript-measurable). A result that changes the conclusion: risk-per-cost and
decision-entropy-per-cost both pay `M`, but WORLD-entropy-per-cost pays `d` and
is optimal — so "greedy acquisition fails" is false as stated; the failure is
specific to scoring the decision variable.

---

## First pass

16 modules in `work/p13_conjectures/`, **68 audits, every one
`{propext, Classical.choice, Quot.sound}`, 0 failures**. Every receipt has
`lean_exit = 0`, unchanged source hash across the compile, and an `.olean`
strictly newer than its source. The 13 pre-existing batch modules were
recompiled from source in this repository rather than having their `.olean`
copied from the other checkout.

| module | audits | package |
|---|---:|---|
| LeanFunctionalContrastDesignV1 | 5 | R1 |
| LeanFunctionalContrastInfimumV1 | 3 | R1 |
| **LeanFunctionalContrastPotentialV1** | 5 | R1 (new) |
| LeanFunctionalOneCellInformationV1 | 6 | R1 |
| LeanD6QueryWidthInformationV1 | (already installed) | R2 |
| LeanD6WidthCostInformationV1 | 3 | R2 |
| LeanD6ScalarWidthRegionV1 | 4 | R2 |
| **LeanD6ScalarWidthSharpV1** | 5 | R2 (new) |
| LeanD6ApproximateActualEvaluatorV1 | 3 | R2 |
| LeanStructuralBudgetRecourseV1 | 5 | R3 |
| LeanStructuralRandomMenuExactV1 | 4 | R3 |
| LeanSupportIntervalHittingV1 | 2 | R4 |
| LeanSupportCyclicWindowV1 | 5 | R4 |
| LeanSupportNonadaptiveLowerV1 | 2 | R4 |
| LeanSupportNonadaptiveExactV1 | 5 | R4 |
| **LeanSupportPassiveDecisionMassV1** | 6 | R4 (new) |
| LeanQueryCriticalResolutionV1 | 5 | R5 |

---

## R2 — the `mu < 1/2` region is now characterised

**The region was never a gap; the sweep stopped below it.**

Reading the published proof of `joint_mixture_scalar_bound`, the hypotheses
`1/2 ≤ mu` and `width ≤ cost*variance` are used only to produce one inequality:

    (1 - mu)^2 * width  <=  mu^2 * (cost * variance).                      (*)

`LeanD6ScalarWidthSharpV1.joint_mixture_scalar_bound_sharp` assumes (*) directly.
The old statement is re-derived as `joint_mixture_scalar_bound_of_half`, so
nothing is weakened. `sharp_of_ratio` shows (*) holds whenever
`cost*variance >= width*((1-mu)/mu)^2`, for any `mu` in `(0,1]` — below `1/2`
the ratio simply exceeds 1 and the charge has to be larger.

In the power model `cost*variance = width^z`, (*) reads
`(1-mu)^2 * width^(1-z) <= mu^2`. For `z > 1` the binding width is the smallest
admissible one, 2, so the threshold is

    z*(mu) = 1 + 2*log((1-mu)/mu)/log 2,   z*(1/4) = 4.1699,  z*(2/5) = 2.1699.

The published 48-cell sweep runs to `z = 2.5` only, which is why it contains no
scalar-optimal cell below `mu = 1/2`.

**Confirmed on the same solver** (`scripts/R2_below_half_threshold.py`, 16 cells
at `q = 3,4`, `mu = 1/4, 2/5`, `z` straddling `z*`; primal-dual gap `< 1.7e-8`):

| q | mu | z | z* | value | mu^2/(2q) | optimal design |
|---|---|---|---|---|---|---|
| 3 | 0.25 | 3.170 | 4.170 | 0.0180586 | 0.0104167 | width 2 |
| 3 | 0.25 | 3.920 | 4.170 | 0.0110621 | 0.0104167 | widths 1 and 2 |
| 3 | 0.25 | 4.420 | 4.170 | 0.0104167 | 0.0104167 | **scalar only** |
| 3 | 0.40 | 1.920 | 2.170 | 0.0274886 | 0.0266667 | width 2 |
| 3 | 0.40 | 2.420 | 2.170 | 0.0266667 | 0.0266667 | **scalar only** |
| 4 | 0.25 | 4.420 | 4.170 | 0.0078125 | 0.0078125 | **scalar only** |

All 16 cells match the prediction: above `z*` the optimum equals `mu^2/(2q)` with
all cost mass on width 1; below it the scalar value is strictly beaten.

### What R2 does NOT establish

- (*) is SUFFICIENT for the mixture certificate, and the mixture is an upper
  bound on a design's value. The final "hence the scalar design is optimal"
  assembly with `uniform_B_lower` remains prose in `WIDTH_SCALAR_REGION_PROOF.md`,
  not a Lean theorem.
- The converse — that the scalar design is strictly suboptimal whenever (*)
  fails — is not proved. It is observed at every cell tested.
- `Real.rpow` appears in no statement; the threshold formula is docstring only.
- 16 cells at two `q` and two `mu`. Not a proof over the parameter space.

---

## R3 — the fixed-epsilon recourse question, answered on two axes

`scripts/R3_recourse_scaling.py`, **168 exact rational DP searches**, equal seed
count (6) at every `m` — the published 72-search probe used 8/8/6 seeds across
`m`, so its maxima were not comparable across `m` and could not settle the
`m`-axis. Max `R_eps` per cell:

| epsilon | m=6 | m=8 | m=10 | m=12 |
|---|---:|---:|---:|---:|
| 1/4 | 0 | 0 | 0 | 0 |
| 1/10 | 0 | 0 | 0 | 0 |
| 1/20 | 1 | 0 | 1 | 0 |
| 1/50 | 1 | 2 | 1 | 3 |
| 1/200 | 1 | 2 | 3 | 3 |
| 1/1000 | 1 | 2 | 3 | 3 |
| 0 | 1 | 2 | 3 | 3 |

Three findings:

1. **At `eps >= 1/10`, `R_eps = 0` at every `m` tested** — a fully nested chain
   of `eps`-good sets exists, so no deletion is ever forced. This is the clean
   positive half.
2. `R_eps` **saturates** at its `eps = 0` value once `eps <= 1/200`: shrinking
   the tolerance further buys nothing.
3. In between, the maximum trends upward with `m` (1, 2, 3, 3 at `eps <= 1/200`).
   This is evidence AGAINST a bound depending on `eps` alone, and for growth with
   `m` at small tolerance.

### What R3 does NOT establish

- Random integer support matrices, 6 seeds per `m`, `m <= 12`. `m >= 14` was
  skipped (the DP transition is quadratic in the layer size) — stated, not
  silently truncated.
- The upward trend is non-monotone (`m = 10` exceeds `m = 12` at `eps = 1/200`
  in the earlier unequal-seed run). Six draws per cell is a maximum over a small
  sample; this is evidence, not a growth theorem.
- No adversarial family forcing large `R_eps` was constructed, and no uniform
  bound was proved. The `eps >= 1/10 ⟹ R_eps = 0` observation is also not proved.

---

## R4 — the positive condition for passive certification

The negative theorem (`PASSIVE_DECISION_MASS_PROOF.md`) says a vanishing-mass
dangerous tip defeats any passive procedure. The positive condition must
therefore constrain only the decision-relevant region — and in the multi-tip
geometry `zero_radius_iff` pins that region exactly: decision `j` is safe in
world `W` iff `j ∉ W`, so the region for `j` is the single tip `j`, not the whole
support.

`LeanSupportPassiveDecisionMassV1` proves, against the real `selectedRadius`:

* `safe_of_unseen` — on a complete sample, every unseen tip is genuinely safe;
* `unsafe_of_seen` — every seen tip is genuinely unsafe;
* `certification_exact` — so the observed classification is exact, not merely
  conservative;
* `exists_certified_safe` — a certified safe decision exists whenever some tip
  is unseen;
* `one_minus_le_exp_neg_pow` — `(1-gamma)^N <= exp(-(gamma*N))`;
* `sample_size_suffices` — `log(M/delta) <= gamma*N` implies
  `M*(1-gamma)^N <= delta`.

Read together: if every present tip carries mass at least `gamma`, then
`N = O(log(M/delta)/gamma)` samples leave total miss budget `delta`; on that
event the sample is complete and the first four theorems convert it into a
certified safe decision.

### What R4 does NOT establish

- **The probabilistic step is not formalised.** That a mass-`gamma` set is missed
  by `N` i.i.d. draws with probability at most `(1-gamma)^N`, and the union bound
  over tips, are the *reading* of two real-number inequalities. No measure space,
  product measure or sampling process appears in any statement.
- `safe_of_unseen` assumes completeness; it does not say the learner knows the
  sample is complete. That is what the mass assumption buys, and only with
  probability `1-delta`.
- One tip per decision. Heterogeneous tips, correlated supports, and danger
  regions larger than a point are not covered.
- Without a mass lower bound the hypothesis is unusable, since `gamma` may be
  arbitrarily small — the negative theorem is untouched.

---

## R1 and R5 — unchanged from the install pass

R1 gained `LeanFunctionalContrastPotentialV1` (potential upper certificate,
discrete Green identity, Cauchy-Schwarz flow lower certificate). Dirichlet /
Thomson duality, star and path in Lean, and the unknown-extrema topology design
remain open. R5 is as installed.

## Still open after this pass

- **R1**: duality (so the two certificates become the formula `J_c = delta^2/(2 R_eff)`);
  star/path in Lean; unknown-extrema topology; distance-dependent edge costs.
- **R2**: the converse of (*); the Lean assembly of scalar optimality.
- **R3**: an adversarial family forcing large `R_eps`, or a proof of the
  `eps >= 1/10 ⟹ R_eps = 0` observation.
- **R4**: the probability layer; heterogeneous geometry.
- **R5**: a positive bundle-size theorem beyond the `min(d, M)` budget cliff.

## Re-run

```
python3 scripts/compile_receipt_v2.py <module>          # per-module receipt
.venv/bin/python scripts/R2_below_half_threshold.py     # 16 solver cells
python3 scripts/R3_recourse_scaling.py                  # 168 exact DP searches
```
