# `paperA_mechanism.json` — launch source, current source, and why it was not rerun

Recorded 2026-09-23. **The artifact is valid for what it measures and was not rerun.**
The producer has changed since the launch, but no change touches sampling, allocation,
stopping or any computed number. Per the completion specification (§5, "if the algorithm
did not change, do not rerun expensive sampling merely to obtain a new docstring hash:
record the two source versions and the nonsemantic diff instead"), this note records both
versions and classifies every hunk.

## The two source versions

| | SHA-256 of `scripts/EXP_paperA_mechanism.py` |
|---|---|
| launch source (recorded in the artifact as `source_sha256`; equals commit `51a3364`) | `66b6507ad061eb43e7de37040748a3ab0694258d5436679c1c80a62f7a2a390e` |
| current source (after the post-run corrections below) | `1c36d0d737ed5b15541c6e87bd850acafa1e152358e60b8e87d54252a9c2dd17` |

The artifact was written at 2026-09-23 15:11 by the launch source; its five self-checks
pass (`all_passed = true`). Configuration: `r ∈ {1,2,4,8}`, `M = 1`, `alpha = 0.05`,
24 runs per rule and `r`, budget 60000.

## Every hunk of the diff, classified

| Hunk | Kind | Effect on the artifact |
|---|---|---|
| Module docstring, "THE ALTERNATIVES …" (applied from `research/papers/POST_RUN_A_CLAIM_CORRECTIONS_20260923.patch`, base hash verified) | wording | none. The old text described a union of SINGLE half-spaces; the code has always used `min over pairs of max over the pair's two rows`. |
| "WHAT IS COMPARED", GEOMETRY line | wording | none |
| `w_geometry` docstring | wording | none. The old text said "the true game … projected ascent"; the code has always been Nelder–Mead on `value_at`. |
| frontier key `J_true` → `J_true_lower_at_mixture` (three lines) | key name | **schema only.** In the existing artifact, `rows[*].frontier[*].J_true` is exactly what the current source calls `J_true_lower_at_mixture`: the `value_at` lower certificate at the mixture design, never the true value. Readers of the existing artifact must use the old key. |
| `"certificate"` description string | wording in the output | the existing artifact's `certificate` string ("the minimum over half-spaces") is superseded wording; the computation it describes is `value_at` as above. |
| new output fields `geometry_rule_solver`, `geometry_rule_objective` | metadata | absent from the existing artifact. Their content is fixed text about the solver (Nelder–Mead, no global-optimality certificate) and the objective (`value_at`, a lower bound); nothing is computed. |

No hunk changes `value_at`, `halfspace_min`, `half_spaces`, the rules, the RNG recipe
(`default_rng(20260922)`, per-rule seeds), the stopping test, the budget, or the censoring.

## Reading the existing artifact correctly

* Every `J_true_lower_at_*` value, and `frontier[*].J_true`, is a LOWER certificate from
  `value_at`, not exact `J`.
* The GEOMETRY rule's design is the design the Nelder–Mead search found, not a certified
  optimum.
* A proxy run censored at the budget has not been shown never to terminate.

A future rerun of the current producer must write to a NEW path; this artifact is kept as
the launch record.

## Audit addendum (2026-09-24): what the runs are

Result-to-algorithm check of `run()` and `value_at()` in the launch source. No bug was
found, but there is one scope fact every reader must carry.

* **The stopping test certifies answer A only.** `run()` stops when
  `value_at(...) > threshold and ans == "A"`. `half_spaces(r)` covers only the alternatives of
  "retain A is wrong", and the GEOMETRY rule optimises that same A-certificate. The answer at
  the truth is therefore fixed in advance, and no run can stop with B. The three rules are an
  ALLOCATION DIAGNOSTIC under one shared certificate. They are not δ-correct learners.
  `correct == n − censored` holds for every rule and `r` because of this, not because of
  learning. The swap panel (`paperA_swap.json`) is the evidence for the learning question.
* **The certificate is a valid lower bound.** It relaxes the strict centred alternative set to
  a union of polyhedra, dropping the centring constraint, which enlarges the set. Each
  polyhedron is bounded below by the larger of its two exact half-space minima. Both steps
  lower the infimum, so the bound is conservative, not optimistic. It is floating point. The
  martingale weight `N²/(a+N)` and the threshold `log(1/α) + ½Σ log(1+N/a)` match `Qstat`
  and `bthr`.
* **Information access.** `theta` enters only through the simulated observations; the rules
  see the running estimate.

Figure `paperA_mechanism.pdf` (`scripts/FIG_paperA_mechanism.py`, checks in
`paperA_mechanism_figure.json`, 7/7) draws this artifact with that label, and states it in
the paper A caption.
