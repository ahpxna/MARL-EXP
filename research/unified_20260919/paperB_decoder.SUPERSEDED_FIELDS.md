# `paperB_decoder.json` — which fields are superseded, and by what

Recorded 2026-09-23. **The raw counts in this artifact are valid and were not resampled.**
Two derived fields in it are not, and are superseded by a separate analysis of the same
counts. This note exists so that a provenance check does not pass silently over a producer
hash that no longer matches, and so that no figure or caption reads the superseded fields.

## What is still valid

`results` — every per-cell record, including `bad`, `reps`, `m`, `h`, `world`,
`N_per_query`, `total_budget`, `zero_query_floor` and `floor_task`. These are the
observations. Nothing about them changed.

`gap_rows`, `order_rows`, `lower_bound_rows` — exact/enumerated quantities, unaffected.

## What is superseded

Inside `certified` and `censored`:

| Field | Why it is wrong |
|---|---|
| `ruled_out_N` | Took the LARGEST tested rung below the certified one whose CP lower bound exceeded `delta`. A fixed decoder's true error is not known to be monotone in `N`, so one failing rung below a success excludes nothing between them. Only a CONTIGUOUS PREFIX of tested budgets, every rung of which is proved to fail, bounds the first successful tested budget from below. |
| `bracketed` | Derived from `ruled_out_N`, so it inherits the same defect. |

Also, `confidence_family_size` / `per_interval_confidence` in this artifact spend `0.05/J`
on EACH of the lower and upper tail. Used jointly that is a Bonferroni failure bound of
`0.10`, not `0.05`. The per-tail budget must be `0.05/(2J)`.

## What replaces them

`research/unified_20260919/paperB_decoder_grid_v2_20260923.json`, produced by
`scripts/ANALYSE_paperB_decoder_grid_v2.py` **without generating any observation**. Its
`input_sha256` and `input_producer_sha256` were verified against this artifact on
2026-09-23 and match exactly, so it analyses precisely these counts.

It uses `0.05/(2J)` per tail and a contiguous failed prefix, and reports
11 upper-certified panels, 6 with a failed prefix as well, and 5 without an upper
certificate. The identification slope interval at `m = 3` is `[-5.59, -1.07]`, which
contains both `-2(m-1) = -4` and the safe decoder's `-2`.

`scripts/FIG_new_panels.py` reads the v2 artifact for the error bands, and the Paper B
caption states the corrected counts and the slope interval.

## Producer hash divergence, stated plainly

`paperB_decoder.json` records `source_sha256 = bb8d6f14...`, the producer as launched.
`scripts/EXP_paperB_decoder.py` on disk now hashes to `d37b521b...`. The difference is
**semantic**, not wording: the producer was repaired to use `0.05/(2J)` per tail and a
contiguous failed prefix, so a rerun would produce different `certified` rows.

The producer was NOT rerun, deliberately: the specification says not to resample B merely
to obtain corrected intervals, and the corrected intervals already exist in the v2 analysis
of the same counts. A future run of the repaired producer should write to a NEW path rather
than overwrite this artifact.
