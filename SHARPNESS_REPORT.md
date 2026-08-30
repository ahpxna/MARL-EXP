# D6 Sharpness Report

## S1 — approximation constant

Status: `PROVED`.

`S1_D6_approximation_constant_sharp` constructs a valid two-coordinate product-reference world. Its product surrogate has pointwise residual exactly one, while a mixed difference is exactly one. Consequently any universal coefficient smaller than `(m - 1)` already fails at `m = 2`.

Exact searches independently attained the approximation ratio 1:

- 668 nonzero-delta binary `m=2` anchored-product worlds;
- 78,070 nonzero-delta binary `m=3` worlds on value alphabet `[-2,2]`;
- the `m=3` equality witness has `sup |F-Aq| = 2 delta`.

## S2 — decision factor

Status: `IMPROVED_BOUND_CANDIDATE`, not a theorem.

The current verified decision theorem uses `2 (m-1) delta`. Exact searches did not attain it:

- exhaustive anchored `m=3`, 78,070 nonzero-delta worlds;
- exact Fraction q-grid, 61,452 worlds, with each Bernoulli product coordinate in `{0, 1/2, 1}`;
- best observed regret was `1/4` of `2 (m-1) delta`, equivalently `(m-1) delta / 2`.

The latter is only a candidate better constant. No Lean theorem claims it and the current D6 theorem remains valid.

## S3 — joint saturation

Status: `OPEN`.

No searched family jointly saturated the approximation and decision constants. The search did find approximation-equality worlds, but their decision regret did not saturate the existing factor.

Raw evidence:

- `compile_logs/d6_sharpness_results.json`
- `compile_logs/d6_sharpness_m3_range2.json`
- `compile_logs/d6_decision_qgrid_results.json`

## q-sensitive results

Q1–Q4 are proved for the exact hybrid telescoping identity used by D6. Q3 is safe only in this typed form: it averages the signed mixed differences at the same hybrid arguments appearing in the residual identity. Q5 is a separate distributional decision theorem and is conditional on surrogate optimality for `qL1CompressionLoss`; it does not silently transfer a worst-case objective into a distributional one.
