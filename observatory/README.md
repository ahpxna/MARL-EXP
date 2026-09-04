# CIG-AMF Observatory

A measurement layer that runs *beside* the existing labs in `research_chains/`
and `scripts/`. It does not replace them and does not modify them, so every
historical result keeps its provenance.

Its job is narrow and deliberate: **record every quantity of every equation of
every chain, on the same worlds, in one long-format store** — then let the
questions be asked afterwards.

## Why long format

One JSONL row is one quantity:

```json
{"record":"q","chain":"D6","eq_id":"D6.half_factor","symbol":"J","role":"lhs",
 "mode":"exact","status":"measured","value":0.375,"exact":"3/8",
 "instance":{"world_id":"...","family":"cartesian","m":3,"k":1,...}}
```

A wide table forces you to decide in advance which columns matter. This store
does not: adding a quantity adds rows, never a schema migration, and a question
nobody thought of on the day of the run can still be answered from the same
file.

Four fields carry the discipline the portfolio already imposes on itself:

- `mode` — `exact` or `float`. Only exact rows may falsify anything.
- `status` — `measured` / `undefined` / `skipped` / `blocked` / `error`.
  *Absence of a number is data.* Conflating "not computed" with "false" was the
  first bug this store caught, in its own writer.
- `role` — `lhs` / `rhs` / `slack` / `ratio` / `flag` / `term` / `input` / `diag`.
  Both sides and the slack of an inequality are always written, including when
  it holds: a satisfied bound with tiny slack is a sharpness witness and is
  invisible if only violations are logged.
- `instance.world_id` — a content hash of the exact world. Without it, rows from
  different worlds that share `(family, m, arity, |Omega|)` are indistinguishable
  and any downstream join silently mixes them.

## Layout

| file | contents |
|---|---|
| `schema.py` | row schema, equation registry, `Emitter` |
| `equations.py` | all 55 equations and their ~500 symbols, with ledger status |
| `exact.py` | rational primitives: oscillation, gauge error, extrema gaps, Top-k |
| `worlds.py` | exact finite worlds, structural families, named witnesses |
| `chains/` | one probe per chain: `support`, `master`, `structural`, `d6`, `functional`, `query`, `cross` |
| `screen.py` | vectorized float screening (optional GPU) that feeds the exact probes |
| `run.py` | sweep driver with profiles |
| `mine.py` | coverage, violations, tightness, discovery, correlations, regimes |

## Running

```bash
python -m observatory.run  --profile quick --out research/observatory
python -m observatory.mine research/observatory --out research/observatory/analysis
```

Profiles are `smoke`, `quick`, `screening`, `deep`. `quick` takes about half a
minute and writes ~250k rows.

## What the miner answers

1. **Coverage** — declared symbols that never got emitted. A silent
   instrumentation gap looks exactly like a quantity that is always zero.
2. **Violations** — every row where a declared claim failed, with the full
   instance key so the world can be rebuilt exactly. Expected findings (the
   already-falsified `m-1` law, "local does not imply global") are listed
   separately from genuine surprises.
3. **Tightness** — smallest non-negative slack per equation. Zero slack is a
   sharpness witness; a bound that is never close to tight is either loose or
   being measured on the wrong family.
4. **Discovery** — pairs `(X, Y)` with `X <= Y` on every jointly measured
   instance, filtered so that both sides vary, the relation is tight somewhere
   *and* slack somewhere, and it is not a definitional restatement. This is the
   part meant to *generate* conjectures rather than check them.

The discovery pass rediscovers `r_lower <= r_actual <= r_upper` and
`radius_exact <= radius_modular` from data alone, which is the intended
validation; anything it surfaces beyond that is a lead, not a result.

## Screen, then certify

`screen.py` runs large float batches to *rank* candidate worlds by how close
they come to violating a target (currently the half-factor ratio `J`). It never
decides anything. The top of the ranking is lifted back to exact rationals via
`to_exact_world` and re-derived by the exact probes.

`backend_info()` reports whether the batch maths ran on numpy, CUDA or Apple
MPS. The exact layer is `Fraction` arithmetic — arbitrary-precision integers
with no vector unit — so it has no accelerator path and is not meant to have
one. GPUs help the search, not the proof.

## Cost guards

Probes whose cost is quadratic in `|Omega|` or factorial in `m` carry explicit
caps and emit a `skipped` row when they trip. A skipped probe is visible in the
store; a hung sweep is not.
