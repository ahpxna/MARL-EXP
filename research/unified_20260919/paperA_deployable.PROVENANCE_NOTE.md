# `paperA_deployable.json` — deployable policies under one two-answer certificate

Recorded 2026-09-24. Resolves deviation P-1 (true label in the mechanism panel's stop).

| item | value |
|---|---|
| producer | `scripts/EXP_paperA_deployable.py`, sha256 `1197faecbf9cdaeb…` at launch (recorded in the artifact as `source_sha256`) |
| artifact | `research/unified_20260919/paperA_deployable.json`, sha256 `165c4ea009053b72…` |
| interpreter | `.venv/bin/python` (numpy, scipy 1.18.1) |
| seeds | `np.random.default_rng([20260924, r, swapped, rule_index, run_index])`, one stream per run |
| configuration | `M = 1`, `r ∈ {1,2,4,8}`, base and swapped worlds, `alpha = 0.05`, 24 runs per cell, budget `B = 60000`, check every 50 rounds, geometry refresh every 500 rounds |
| wall time | about 45 minutes (r = 8 geometry dominates) |
| self-checks | 6/6 |
| figure | `research/papers/_figures/paperA_deployable.pdf` (`scripts/FIG_paperA_deployable.py`, sha256 `e5737fea7d0a102e…`, 4/4). A first render with an overlapping label is kept at `legacy/figure_rerenders_20260924/` |

## What the rules are, and what they see

All three are tracking learners with a warm start, forcing `min(1, 1/√t)` toward uniform, and
the first argmax of `W − N`. Their oracles see only the running estimate.

- `surrogate_at_estimate`: every round, the frozen surrogate is re-solved at the estimate. The
  estimate's four frozen extremum cells get `w_e ∝ σ_e`. A self-check confirms this is the
  surrogate's exact optimum at random estimates (no random design beats it), and that within
  1/16 of the truth it equals the uniform-anchor design (`surD_middle_zero`, M = 1).
- `geometry`: a Nelder–Mead ascent of the certificate of the answer the estimate retains.
- `uniform`.

**Information access.** No rule reads `theta`. The true world enters only through the
simulated observations. The stop no longer uses the true answer. Each run stops when the
certificate of the answer its estimate retains clears the threshold, and it returns that
answer. That certificate is either of the two covers of `EXP_paperA_swap.py`.

## What was measured

- Across the whole panel, 505 runs stopped and none returned the wrong answer. The binomial
  tail check against alpha passes.
- On the base world (answer A), the surrogate learner certified in 22, 3, 0 and 0 of 24 runs
  at r = 1, 2, 4, 8. Geometry and uniform certified every run.
- On the swapped world (answer B), every rule certified every run.
- Along every run, every middle cell obeys `N_e ≤ 2 + bad_e + q(t)`, the transcription of
  `oCount_le_bad` for the code's forcing. The minimum slack is 0.33.

## Scope

- The stop's certificate is a valid LOWER bound on the retained answer's GLR. It is not the
  exact infimum used by `tauG`.
- alpha = 0.05 is far above the `delta_0` of `surrogate_learner_cost`.
- `bad_estimate_rounds` (an estimate off by 1/16 or more) is close to `tau` in most runs.
  Within 6·10⁴ rounds the forced middle counts are still small, so this horizon lies far
  inside the pre-asymptotic regime.

So the panel is evidence about these rules on this family. It is not a test of the
`Ω(log²(1/δ))` order.
