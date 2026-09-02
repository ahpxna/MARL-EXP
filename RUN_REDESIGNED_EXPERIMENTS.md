# Redesigned CIG-AMF experiments — execution order

Run these after applying the cumulative redesign patch.  Development/falsification
artifacts must not be relabeled confirmatory.

## 0. Release gate

```bash
python -m compileall -q envs research_chains scripts tests
python -m scripts.run_release_tests -q
```

## 1. Adapter capability audit

Static, no external runtime needed:

```bash
python -m scripts.run_adapter_capability_audit \
  --adapters omni rware flatland cyborg cityflow \
  --out research/external/ADAPTER_CAPABILITY_STATIC.json
```

Install/verify pinned external runtime:

```bash
bash scripts/setup_external_envs.sh --install
python scripts/external_env_manager.py status --json research/external/EXTERNAL_STATUS.json
```

Runtime audit:

```bash
python -m scripts.run_adapter_capability_audit \
  --runtime --adapters rware flatland cyborg cityflow \
  --seed 3001 --out research/external/ADAPTER_CAPABILITY_RUNTIME.json
```

## 2. Coupled honored-support probe

Run RWARE first, then Flatland.  A positive result is about **resolved/honored
support**, not requestable command support.

```bash
python -m scripts.run_external_coupled_support_probe \
  --adapter rware --seed 3001 --n-states 64 --n-sources 2 --max-cells 256 \
  --out research/external/rware_honored_support_2.json

python -m scripts.run_external_coupled_support_probe \
  --adapter rware --seed 3002 --n-states 64 --n-sources 3 --max-cells 512 \
  --out research/external/rware_honored_support_3.json

python -m scripts.run_external_coupled_support_probe \
  --adapter flatland --seed 3001 --n-states 64 --n-sources 2 --max-cells 256 \
  --out research/external/flatland_honored_support_2.json
```

If execution receipts are unverified, the adapter is blocked; do not coerce the
result to Cartesian/non-Cartesian.

## 3. Unknown-variance Functional redesign

```bash
python -m scripts.run_functional_unknown_variance_lab \
  --instances 2000 \
  --seeds 100 101 102 103 104 \
  --budgets 32 64 128 256 512 \
  --actions 6 --alpha 0.05 \
  --out research/high_value_extensions/functional/unknown_variance_deep.json
```

`known_sigma_oracle` is diagnostic only.  Primary comparisons are uniform,
variance plug-in, shrinkage, and the repeated-look t-radius proxy.  Report
selection-error fraction separately from variance-relative error.

### 3b. Fixed-confidence learn-variance-then-exploit

The historical fixed-budget `C_successive` comparison is not a deployable
headline. Use the redesigned fixed-confidence experiment:

```bash
python -m scripts.run_functional_variance_stopping_lab \
  --instances 1000 --seeds 100 101 102 103 104 \
  --relations 5 --actions 6 --topk 2 --alpha 0.05 \
  --max-n 16384 --batch 16 --pilot-fraction 0.15 \
  --out research/high_value_extensions/functional/variance_stopping_deep.json
```

Deployable variants are `uniform`, `C_split`, `C_pilot`, `C_shrink`, and
`C_anytime`. `C_known_sigma` is an oracle ceiling only. The primary endpoint is
`N_certificate`, not C-MAE.

## 4. Response/reference budget split

```bash
python -m scripts.run_reference_response_budget_lab \
  --instances 1000 \
  --seeds 100 101 102 103 104 \
  --budgets 64 128 256 512 1024 \
  --splits 0 0.1 0.2 0.3 0.5 0.7 0.9 \
  --relations 4 --actions 3 --topk 2 --alpha 0.05 \
  --out research/high_value_extensions/master/reference_response_budget_deep.json
```

Required outputs are exactly:
`Q_error`, `kernel_tv`, `chi_error`, `final_score_interval_width`,
`topk_regret`, `certificate_coverage`.

## 5. MASTER certificate frontier

The current MASTER runner already sweeps a frontier around the requested
operating tolerance.

```bash
python -m scripts.run_master_extension_lab \
  --instances 5000 --budgets 16 32 64 128 256 512 \
  --seed 100 --tolerance 0.20 \
  --out research/high_value_extensions/master/deep_frontier.json
```

Do not select one tolerance post hoc as universal. Plot certified/fallback
fraction, empirical/worst certified regret, false-safe rate, runtime saved,
certificate computation cost, bound width, and Gamma-box/Gamma-op ratio over
the frozen frontier `0,.01,.02,.05,.1,.2,.3,.5,1`.

## 6. D6 theorem attack: exhaustive → directed optimizer → Lean proof attempt

### 6a. Exhaustive exact integer worlds

```bash
python -m scripts.run_d6_exact_small_search \
  --m 3 --k-values 1 2 --value-radius 1 \
  --q-grid 1/4 1/2 3/4 \
  --out research/high_value_extensions/d6/exact_m3_r1.json
```

Then expand the exact lattice if tractable:

```bash
python -m scripts.run_d6_exact_small_search \
  --m 3 --k-values 1 2 --value-radius 2 --stop-on-counterexample \
  --out research/high_value_extensions/d6/exact_m3_r2.json
```

### 6b. Counterexample-directed optimization

```bash
for k in 1 2; do
  python -m scripts.run_d6_counterexample_optimizer \
    --restarts 10000 --steps 500 --m 3 --alphabet 2 --k "$k" --seed $((700+k)) \
    --out "research/high_value_extensions/d6/optimizer_m3_k${k}.json"
done

for k in 1 2 3; do
  python -m scripts.run_d6_counterexample_optimizer \
    --restarts 5000 --steps 300 --m 4 --alphabet 2 --k "$k" --seed $((800+k)) \
    --out "research/high_value_extensions/d6/optimizer_m4_k${k}.json"
done
```

Any ratio `> 0.5` kills the half-factor conjecture.  Survival is **not proof**.

### 6c. Lean proof attempt

Use the same pinned environment recorded in `LEAN_EXECUTION_LEDGER_HIGH_VALUE.md`:
Lean `4.34.0-rc2`, Mathlib commit
`1f495c611d05d2215058cd77c7897d625bc3b445`.
Copy the active P12 `.lean/.olean` files and the scratch P13 module into an
isolated build directory, use the same `LEAN_PATH` recipe as
`compile_logs/run_high_value_build.sh`, then compile:

```bash
$LEAN -o LeanD6DecisionHalfFactorConjecture.olean \
  LeanD6DecisionHalfFactorConjecture.lean
```

While it contains `sorry`, it stays quarantined.  Replace `sorry`; compile exit
0; run:

```bash
grep -Rnw work/p13_conjectures -e 'sorry' -e 'admit' -e '^axiom '
```

Only a zero-sorry proved module may be promoted into P12.

## 7. Diagnose why Omni D6 regret is zero

Vary source set, outcome role, state bank and m; do not only increase random
world count.

```bash
for seed in 3001 3002 3003 3004 3005; do
  python -m scripts.run_omni_d6_full_joint \
    --seed "$seed" --m-sources 3 --n-states 16 --warmup-steps 5 \
    --out "research/high_value_extensions/d6/omni_causes_${seed}.json"
done
```

Explicit role permutations:

```bash
python -m scripts.run_omni_d6_full_joint \
  --seed 3001 --m-sources 3 --source-agents 0 1 2 --outcome-agent 4 \
  --n-states 16 --warmup-steps 5 \
  --out research/high_value_extensions/d6/omni_roles_a.json
```

Inspect `zero_regret_cause_counts`, `delta_square`, `topc_score_margin`,
`exact_optimality_gap`, and `empirical_margin_shield_condition`.

## 8. External Query transfer

All methods derive from the same frozen state/intervention panel.  The runner
uses mathematical primitives, not falsely branded full-paper implementations.

```bash
for env in rware flatland cyborg cityflow; do
  python -m scripts.run_external_query_transfer \
    --adapter "$env" --seed 3001 --n-states 32 --warmup-steps 3 \
    --k 2 --n-candidates 4 \
    --out "research/external/query_transfer_${env}.json"
done
```

Primary endpoint: `query_regret`.  Secondary: Top-K exact and Spearman.
Message deletion, communication delay, and VoI remain blocked/NA until an
adapter exposes those interventions.

## 9. V7 confirmatory

Keep the already frozen 20-seed protocol.  Do not tune using confirmatory data.

```bash
python -m scripts.run_h1_fixed_panel_confirmatory --dry-run \
  --seeds 5001 5002 5003 5004 5005 5006 5007 5008 5009 5010 \
          5011 5012 5013 5014 5015 5016 5017 5018 5019 5020 \
  --device cpu --out-root research/confirmatory_functional_v2_fresh

python -m scripts.run_h1_fixed_panel_confirmatory \
  --seeds 5001 5002 5003 5004 5005 5006 5007 5008 5009 5010 \
          5011 5012 5013 5014 5015 5016 5017 5018 5019 5020 \
  --device cpu --out-root research/confirmatory_functional_v2_fresh
```

The underlying V7 runner validates and skips complete cells. This is the
supported resume path and does not rerun a valid completed cell from the same
evidence protocol. It fails closed instead of relabeling older development
cells as confirmatory, so the first confirmatory run must use a fresh root.

## 10. Structural

Do not restart broad exact-iff search. Attack only the surviving approximate
candidate with exact-small enumeration and a directed falsifier:

```bash
python -m scripts.run_structural_counterexample_search \
  --mode exact \
  --out research/high_value_extensions/structural/exact_m3.json

python -m scripts.run_structural_counterexample_search \
  --mode directed --restarts 1000 --steps 200 --seed 9001 \
  --out research/high_value_extensions/structural/directed_m456.json
```

Any positive `candidate_violation` kills
`best_nested_max_regret <= m * all_optimal_extension_defect`. Survival remains
falsification evidence, not proof. Runtime from `run_structural_defect_lab`
remains an algorithmic diagnostic; the 91,130-world exact-iff search stays
closed.
# Current release corrections

## Confirmatory evidence root

`research/confirmatory_functional/` is a historical interrupted,
development-only root and must not be analyzed or retagged.  Use only the fresh
root below; the analyzer requires `CONFIRMATORY_RUN_COMPLETE.json`, a 60-cell
grid, confirmatory manifest semantics, and confirmatory semantics in every cell.

```bash
python -m scripts.run_h1_fixed_panel_confirmatory \
  --seeds $(seq 5001 5020) \
  --device cpu \
  --out-root research/confirmatory_functional_v2_fresh

python -m scripts.analyze_v7_confirmatory \
  --root research/confirmatory_functional_v2_fresh
```

## D6 half-factor falsification gate

Run the exact coordinate-specific product-reference grid and directed campaign
before serious Lean proof engineering.  Survival is not proof.

```bash
python -m scripts.run_d6_half_factor_campaign \
  --profile deep --seeds 701 702 703 704 705 \
  --seed-witness research/high_value_extensions/d6/current_best_046875.json \
  --resume \
  --out-root research/high_value_extensions/d6/half_factor_deep
```

The proof gate opens only after exact binary coordinate-specific-q, deep m3,
deep m4, m5 directed, and witness-local campaigns complete without `J > 1/2`.
The next proof routes are direct selected-vs-optimal residual comparison,
surrogate Top-C optimality, and oscillation centering.  MILP/SAT/evolutionary
methods are optional only when they answer a specific finite-certification
question; they are not checklist requirements.

## Typed external Query benchmark

```bash
python -m scripts.run_external_query_transfer \
  --adapter rware --seed 3001 --n-states 32 --k 2 \
  --information-budget 128 \
  --out research/external/query_transfer_rware.json

python -m scripts.analyze_external_query_transfer \
  research/external/query_transfer_*.json \
  --out research/external/QUERY_TRANSFER_ANALYSIS.json
```

Missing attention, communication, information, or causal-context providers stay
`BLOCKED_NA` with reason codes.  No foreign score is substituted.

## Post-P13 novelty-critical experiment layer (2026-09-01)

The research reports were reframed around **proof/certificate objects**, not
"active acquisition" as a standalone novelty claim.  The following runners are
new development experiments.  They do not delete or supersede historical
artifacts; write them under `research/novelty_critical/`.

```bash
python -m scripts.run_typed_certificate_completion_lab --instances 1000 --seed 6101
python -m scripts.run_functional_selective_maintenance_lab --instances 2000 --seed 6201
python -m scripts.run_support_critical_identification_lab --instances 500 --seed 6301 --m 4 --k 2 --epsilon .05
python -m scripts.run_structural_prefix_cover_lab --instances 2000 --seed 6401 --m-values 3 4 5 6
python -m scripts.run_d6_cost_aware_paec_lab --instances 2000 --seed 6501
python -m scripts.run_query_identifiability_lab --instances 5000 --seed 6601
```

Scientific scope gates:

- `D6.COST_AWARE_PAEC_COMPLETION` is conditional on an **available valid
  certificate**.  It must never be interpreted as evidence for the still-open
  `EveryTopCPairHasPAEC` theorem.
- `D6.FIRST_ORDER_INSUFFICIENCY_B7` reproduces the exact Lean witness and may be
  reported as a necessity/escalation result.
- Structural prefix-cover runs are search/falsification evidence.  Finding no
  `chi>=3` world is not a theorem; an exact witness should be ported to Lean
  before promotion.
- Query identifiability is a typed semantic verifier.  Natural-language XAI
  technique routing is not the novelty headline and external real-method
  transfer remains a separate requirement.
- Functional maintenance uses an idealized refresh model first; external MARL
  drift experiments must later replace synthetic drift before deployment
  claims.

Before interpreting archived results after changing source/registry, run:

```bash
python -m scripts.audit_post_p13_results --root . --out research/post_p13_result_audit.json
```

The audit is append-only: it marks old artifacts `STALE_*`/`INCOMPLETE` but does
not rewrite them.

### One-command novelty-critical suite

For a cheap plumbing/smoke run:

```bash
python -m scripts.run_novelty_critical_suite --profile quick
```

For the planned development screening sizes:

```bash
python -m scripts.run_novelty_critical_suite --profile screening
```

Each child runner writes its own provenance sidecar. `SUITE_SUMMARY.json` is orchestration metadata only. Historical result directories are not rewritten by the suite.

When auditing an older result-rich checkout against the current source tree, keep the two roots explicit:

```bash
python -m scripts.audit_post_p13_results \
  --root /path/to/historical/result_checkout \
  --source-root . \
  --out research/post_p13_historical_result_audit.json
```

This comparison never rewrites the historical checkout.
