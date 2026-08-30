# CIG-AMF V7 — Fixed Evaluation Panel + Two-Level Functional Margins

V7 is a development experiment built on the canonical source chain:

```text
V4 chain-harness source
  -> V5 Omni support/oracle patch
  -> V6 functional-boundary patch
  -> V7 fixed-panel/two-level-margin patch
```

## Why V7 exists

V6 established a clean local theorem-backed phase boundary:

```math
\delta_{Q,j}^{\circ} < g_j/2
\Rightarrow
\text{the true max/min action identities for relation }j\text{ are preserved.}
```

In the V6 development archive, 691 rows satisfied the certified condition and
there were zero extrema-stability violations.  However, the fraction of
low-`lambda_C` rows did not explain seed-level global C ranking.  In addition,
20/80/320 used different held-out state populations, so apparent movement of
`lambda_C` across training budgets was composition-confounded.

V7 fixes both issues.

1. Every training checkpoint for one seed is evaluated on the exact same hashed
   oracle panel, including environment state, factual joint action, target
   policy, valid action mask and raw evaluation context.
2. It separates two selection layers:
   - within-relation extrema stability (`lambda_C`);
   - between-relation C-ranking / Top-K stability (`lambda_topk_Q`).
3. It adds the theorem-backed directional sign phase:

```math
\lambda_D=
\frac{\|\pi-q\|_1\delta_Q^\circ}{|D|}<1
\Rightarrow
\operatorname{sign}(\widehat D)=\operatorname{sign}(D).
```

## Main command

From the repository root:

```bash
source .venv/bin/activate

python -m scripts.run_h1_fixed_panel_v7 \
  --seeds 3001 3002 3003 3004 3005 \
  --checkpoints 20 80 320 \
  --tiny-states 24 \
  --max-steps 30 \
  --device cpu \
  --out-root /Users/phanan/cig-amf-main/research/v7_fixed_panel
```

The runner creates one immutable fixed panel per seed and reuses it across all
checkpoints.

## Critical outputs

```text
research/v7_fixed_panel/
  v7_manifest.json
  v7_panels.json
  v7_panel_consistency.json
  v7_hard_gates.json
  v7_analysis.json
  v7_pair_panel.csv
  v7_state_panel.csv
  v7_seed_checkpoint_summary.csv
  v7_checkpoint_summary.csv
  panels/
  runs/
```

### Hard fail-closed checks

`v7_hard_gates.json` must report zero violations for:

```text
local_extrema_theorem_violation_count
capacity_q_error_bound_violation_count
topk_q_certificate_violation_count
topk_interval_certificate_violation_count
direction_sign_certificate_violation_count
```

and:

```text
fixed_panel_oracle_invariance_pass = true
all_deterministic_checks_pass = true
```

`v7_panel_consistency.json` requires oracle range, signed direction, extrema
identities and extrema gaps to agree exactly across checkpoints for the same
hashed panel rows.

## New diagnostics

Per relation:

```text
q_gauge_sup_error
lambda_C
capacity_q_error_bound = 2 * delta_Q_circ
oracle_capacity_rank
learned_capacity_rank
oracle_capacity_topk_member
learned_capacity_topk_member
oracle_capacity_margin_to_topk_boundary
lambda_D
direction_sign_certified
direction_sign_violation
```

Per state/ego:

```text
oracle_topk_gap
capacity_topk_match
lambda_topk_Q
capacity_topk_q_certified
capacity_topk_q_certified_violation
capacity_topk_interval_certified
oracle_full_rank_min_gap
strict_relation_pair_order_accuracy
q_certified_relation_pair_count
q_certified_relation_pair_violation_count
```

## Interpretation

Do not collapse the two C margins.

```text
lambda_C
  -> local action-extrema identity

lambda_topk_Q / oracle_topk_gap
  -> between-relation Top-K stability
```

A seed may have many locally certified relations and still have weak global C
ranking when true relation scores are tightly packed.

Likewise, `lambda_D < 1` certifies direction/sign only.  It does not certify
magnitude ranking across relations.

V7 is development evidence.  It does not alter frozen H1 confirmatory gates or
promote any development seed to confirmatory evidence.

## Resume-safe incremental runs (V7.1 provenance hotfix)

The runner is resume-safe across separate commands. Existing run cells are
validated from their scientific artifacts, not trusted merely because a folder
or marker exists.

If 20/80 are complete and a 320 command was interrupted, re-run the same 320
command. Complete 320 cells are skipped automatically; incomplete cells are
cleared and recomputed:

```bash
python -m scripts.run_h1_fixed_panel_v7 \
  --seeds 3001 3002 3003 3004 3005 \
  --checkpoints 320 \
  --tiny-states 24 \
  --max-steps 30 \
  --device cpu \
  --out-root /Users/phanan/cig-amf-main/research/v7_fixed_panel
```

To rebuild all cumulative 20/80/320 aggregate files without training:

```bash
python -m scripts.run_h1_fixed_panel_v7 \
  --analyze-only \
  --seeds 3001 3002 3003 3004 3005 \
  --checkpoints 20 80 320 \
  --tiny-states 24 \
  --max-steps 30 \
  --device cpu \
  --out-root /Users/phanan/cig-amf-main/research/v7_fixed_panel
```

`v7_manifest.json` is cumulative and records invocation history. The companion
`v7_completion_status.json` separates fully completed checkpoints from partial
checkpoints and lists every incomplete cell. Root CSV/JSON aggregates contain
only validated complete cells.

Use `--rerun-complete` only when intentionally recomputing already complete
cells. By default, complete cells are skipped.

## Final reporting layer (post fixed-panel runs)

The V7 runner now regenerates paper-facing reports from validated complete cells whenever it aggregates or runs with `--analyze-only`. This reporting layer does not change training, estimators, theorem thresholds, or scientific targets.

Additional outputs:

- `v7_paired_longitudinal.csv`: pooled same-panel 20→80, 80→320, and 20→320 paired changes.
- `v7_paired_longitudinal_by_seed.csv`: the same paired changes separately for each development seed.
- `v7_lambdaC_phase.csv`: within-relation phase table for `lambda_C` bins `<0.25`, `0.25–0.5`, `0.5–1`, `>=1`.
- `v7_lambda_topk_phase.csv`: between-relation Top-K phase table for `lambda_topk_Q` bins `<1`, `1–2`, `2–5`, `>=5`.
- `v7_lambdaD_phase.csv`: Q-derived D-sign phase table for `lambda_D` bins `<1`, `1–2`, `2–5`, `>=5`.
- `v7_certificate_nonvacuity.csv`: eligible count, certificate coverage, conditional correctness, and false-safe violations for local extrema, Top-K Q-margin, Top-K interval, and D-sign certificates.
- `v7_phase_correlations.csv`: pooled checkpoint-level Spearman associations between the phase ratios and their relevant errors/selection outcomes.
- `v7_final_scientific_report.json`: machine-readable report index and guardrails.

The reports are valid only when `v7_panel_consistency.json` passes. Certificate coverage is reported separately from certificate correctness: zero false-safe violations must not be interpreted as practical nonvacuity.
