# `paperC_robustness.json`, `paperC_perturbation.json` — result-to-algorithm audit

Recorded 2026-09-24. **Neither artifact was modified or re-run.** This note records what the
stored numbers are, which Lean object they correspond to, and one over-claim in a check name.

## Provenance

Both artifacts were produced by the current source. The SHA-256 of
`scripts/EXP_paperC_robustness.py` (`34d0aa00…`) and of `scripts/EXP_paperC_perturbation.py`
(`89ccb1d4…`) equal the `source_sha256` fields stored in the two JSONs.

## What the stored quantities are

* `paperC_perturbation.json`
  * `rows` (160, group weights, flow LP) and `per_item_rows` (60, the `m!` permutation LP
    with a per-ITEM band) implement Lean's `trueValue`. That means the band
    `|Pr(i ∈ prefix_k) − k/m| ≤ η/m` on every item, the interior budgets `1..m−1`, and the
    objective `max_k E[(|prefix_k| − b_k)/D]`.
  * `drift_movingD` (baseline recomputed for `g'`, `D = ‖g'‖₁`) is exactly the quantity
    bounded by `family_value_robust` (`LeanPaperCStabilityFamilyV1`).
  * `drift_fixedD` and `drift_stale` are different objectives: the normaliser is frozen, or
    the baseline is frozen.
  * **Solver failures are skipped without being recorded.** The producer runs
    `if … is None: continue`. For THIS artifact nothing was dropped: the stored row counts
    equal the fixed grid (5 × 4 × 8 = 160 and 3 × 4 × 5 = 60). A future run would need the
    failures recorded.
* `paperC_robustness.json`
  * `worst_ratio` is the smallest price ratio an adversarial search found. It is an
    ATTAINED example, hence an upper bound on the worst case.
  * `proved_floor` is `price_ratio_robust`, valid for odd `m` and `eps ≤ 1/4`
    (`floor_in_domain`).

## Finding: one check name over-claims

The first check of `paperC_robustness.json` reads:

> "the price survives well beyond the Lipschitz scale … so the proved floor is LOOSE".

A minimising search bounds the worst case from ABOVE only. Attained ratios above the floor
are consistent with the true worst case lying anywhere between the floor and the attained
values. They cannot show that the floor is loose, and a search that finds no collapse bounds
nothing from below.

This is a **wording over-claim, not an algorithmic bug**: the stored numbers are right. The
manuscript sentence that repeated it ("the floor is loose by close to an order of magnitude")
was corrected in `paper_c.tex` on 2026-09-24. The JSON check name is left as recorded, as
historical evidence; cite this note when quoting it.

## New check, from stored numbers only

`scripts/FIG_paperC_endpoints.py` (→ `paperC_endpoint_figures.json`, 10/10) recomputes the
new Lean envelope `3‖g_m − g'‖₁/d`, with `d = min(D₀, D₁)`, from the stored norms. All 220
`drift_movingD` values lie under it; the worst ratio is 0.322. Every in-domain attained ratio
is at or above `proved_floor`. Either violation would have refuted the corresponding theorem.

## Producer change after the audit (2026-09-24)

`scripts/EXP_paperC_perturbation.py` now records every skipped cell (`skipped_cells`,
`n_skipped`): a failed LP, or a perturbation that zeroes a weight. It also refuses to write
without `--out NEW_PATH` or onto an existing file. Nothing else changed; the LPs, the grid,
the RNG and the checks are as launched. The launch artifact `paperC_perturbation.json` was
written by the launch source `89ccb1d4…` and is kept. The current source is `8df922ddeb2b…`.
A smoke run of the new source (scratch output only) gave 0 skipped cells and passed its
checks.

## Correction to a Lean docstring and a map row

`ratio_collapse_lower` / `collapse_two_sided` (`LeanPaperCCollapseV1`) bound the FLOOR
expression `Rat(m, ε)`, between `(1/8)·min(m−1, 1/ε)` and `2/ε`. That locates where the
GUARANTEE stops being linear in `m` (`ε_c = 1/(m−1)`). It does not locate where the
PRICE collapses: that needs an upper bound on the true worst-case ratio, i.e. a proved
destructive perturbation, which does not exist. The module docstring and THEOREM_MAP row C-H4
read as if the price itself were `Θ(min(m, 1/ε))`; both are corrected to the floor.
