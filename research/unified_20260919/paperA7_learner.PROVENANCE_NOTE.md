# `paperA7_learner.json` — launch source, current source, and why it was not rerun

Recorded 2026-09-23. **The artifact is valid for what it measures and was not rerun.**
Every change to the producer since the launch is wording, printed text, or one new
configuration-only self-check; none touches sampling, the oracle, tracking, selection,
stopping or any recorded number. Per the completion specification (§5), the two versions
and the diff are recorded here instead of resampling.

## The two source versions

| | SHA-256 of `scripts/EXP_paperA7_learner.py` |
|---|---|
| launch source (recorded in the artifact as `source_sha256`; byte-identical to the file at commit `51a3364`) | `b329bcba7526bee744fa517e2567bb5164f8ea23bf0dbe7117029059073f8118` |
| base of the prepared correction patch (also the source of `paperA7_learner_smoke.json`, 2026-09-23 15:40) | `0385e141fec6b7841f7fa78b7ab6179e1f61a9832cfba1b628f2f4f42e5b8aa6` |
| current source (patch `research/papers/POST_RUN_A_CLAIM_CORRECTIONS_20260923.patch` applied, base hash verified) | `639b087ad4e6d5b254e5905811a74712b115fc5873bc4a26ee3d23ee0ac16c1c` |

The artifact (2026-09-21 22:50, budget 20000) has 22 self-checks, all passing, and records
its numerical failures (`regional_primal_failed = 12`, all others 0).

## Every hunk of the diff against the launch source, classified

| Hunk | Kind | Effect on the artifact |
|---|---|---|
| Policy docstring, step 1: the radius now shows its `sigma_e` factor | wording | none. The code has always computed `sqrt(var) * sqrt(2(a+N) b_t) / N`. |
| Policy docstring, step 3: `L = 2B/min_e var_e` | wording | none. `lipschitz_modulus(var)` has always returned `2B / min var`, and the artifact records its value in `lipschitz_modulus`. |
| Comment at the oracle schedule | wording | none |
| New self-check "the requested oracle schedule has a positive tolerance floor and a finite iteration cap" | configuration check | absent from the artifact's `checks`. It inspects two constants (`BRACKET_TOL_FLOOR`, `BRACKET_ITERS_CAP`) and verifies configuration only. |
| Four printed lines after it | printed text | none |

## What the artifact does NOT support

These are the corrected claims; they replace any reading of the launch source's comments.

* The oracle schedule is floored and capped, so it does not GUARANTEE `eps_t -> 0`. A
  positive requested tolerance is not a positive lower bound on the ACTUAL solver error.
* Recorded finite-run gaps do not establish a uniform error bound, answer stability, or
  stopping-certificate tightness, so the panel supports neither the exact rate nor a
  finite-eps rate. It reports finite-alpha performance at one world.

A future run of the current producer must write to a NEW path; this artifact is kept as
the launch record. The additional A-F3 panels of the specification (A/B-swapped truths,
two gap regimes, an active-region transition) need a new producer version with explicit
configuration and a fresh output path; they are not obtained by rerunning this one.
