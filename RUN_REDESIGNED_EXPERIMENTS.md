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

## 4. Response/reference budget split

```bash
python -m scripts.run_reference_response_budget_lab \
  --instances 1000 \
  --seeds 100 101 102 103 104 \
  --budgets 64 128 256 512 1024 \
  --splits 0.05 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8 0.9 0.95 \
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

Do not select one tolerance post hoc as universal.  Plot accepted/fallback
fraction, regret guarantee, false-safe count, and runtime over the full frontier.

## 6. D6 theorem attack: exhaustive → directed optimizer → Lean proof attempt

### 6a. Exhaustive exact integer worlds

```bash
python -m scripts.run_d6_exact_small_search \
  --m 3 --k-values 1 2 --value-radius 1 \
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

## 10. Structural

Do not restart broad exact-iff search.  Run the existing deep structural
falsification once more only if the exact Lean definition of the all-optimal
extension defect is ready for the quarantined proof attempt.
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

## 4. Response/reference budget split

```bash
python -m scripts.run_reference_response_budget_lab \
  --instances 1000 \
  --seeds 100 101 102 103 104 \
  --budgets 64 128 256 512 1024 \
  --splits 0.05 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8 0.9 0.95 \
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

Do not select one tolerance post hoc as universal.  Plot accepted/fallback
fraction, regret guarantee, false-safe count, and runtime over the full frontier.

## 6. D6 theorem attack: exhaustive → directed optimizer → Lean proof attempt

### 6a. Exhaustive exact integer worlds

```bash
python -m scripts.run_d6_exact_small_search \
  --m 3 --k-values 1 2 --value-radius 1 \
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

## 10. Structural

Do not restart broad exact-iff search.  Run the existing deep structural
falsification once more only if the exact Lean definition of the all-optimal
extension defect is ready for the quarantined proof attempt.
