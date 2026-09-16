# IEEE conference papers

Seven complete two-column IEEEtran papers, one per strand, each exactly 10 pages
with no overfull boxes and no undefined references.

| file | title | pages |
|---|---|---|
| `master.tex` | The Price of a Calibration Query | 10 |
| `query.tex` | Which Query You Are Allowed to Ask Sets the Leakage Order | 10 |
| `structural.tex` | One Schedule Cannot Serve Every Budget | 10 |
| `functional.tex` | When the Extrema Move, the Scalar Proxy Fails in Both Directions | 10 |
| `d6.tex` | The Slice Is Not a Restriction, and the Design Is Not Fitted | 10 |
| `support.tex` | Deciding Without Identifying | 10 |
| `adaptive.tex` | House Monotonicity and Quota Cannot Both Hold | 10 |

## Building

Requires `tectonic` (installed via Homebrew). From this directory:

```
tectonic -X compile master.tex --keep-logs
```

`./pc.sh <name>` compiles and reports the page count and any errors.

Figures are pulled from `../_figures/` via `\graphicspath` in `preamble.tex`.

## Generated tables

These `.tex` fragments are produced from repository artifacts and are `\input` by
their papers. Regenerate them if the underlying artifact changes.

| fragment | source artifact |
|---|---|
| `master_cells.tex` | `research/worker_P17_master_20260915/`, `worker_P31_master_baselines_20260915/` |
| `query_cells.tex` | `research/worker_P33_query_regret_20260915/` |
| `structural_law.tex` | `work/p13_conjectures/LeanStructuralFamilyLowerV1.lean` (exact rationals) |
| `structural_enum.tex` | `research/worker_STRUCT_enum_20260916/struct_exhaustive.json` |
| `d6_cells.tex` | derived formula, checked against the 24 fitted cells |
| `support_sep.tex` | `research/worker_P20_support_20260915/` |
| `adaptive_trace.tex` | exact simulation of largest-deficit-first |
| `adaptive_search.tex` | `research/worker_ADP_quota_20260916/ADP_quota_search.json` |

## Conventions shared by all seven

- Evidence classes are never mixed: `\PROVED` is machine-checked, `\CERT` is an
  exact rational certificate, `\NUM` is floating point. No numerical result is
  used to support a proved one.
- Each paper carries a "Related work and the novelty boundary" section stating
  what belongs to prior work, read at theorem level.
- Each carries an "Evidence per step" table naming the Lean declaration behind
  every step, and a "What is not established" list.
- The acceptance contract for a Lean module is stated in full in each paper.
