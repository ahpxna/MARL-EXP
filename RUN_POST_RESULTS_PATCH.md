# CIG-AMF post-results + 100-track audit rerun guide

This patch is cumulative against `MARL-EXP-main (3).zip`: it includes the 100-track audit hardening plus the result-driven fixes discovered after the first deep runs.

## Results invalidated and must be rerun

1. **MASTER deep support-uncertainty**: old run had `mean_span_interval_width=0`; generator was vacuous.
2. **Functional matched-budget allocation**: old `C_successive_elimination` used true synthetic sigma, and headline winners could include oracle strategies.
3. **Query deep synthetic transfer**: keep old aligned result as development evidence, but rerun with the new `cross_query_entangled` stress family.
4. **D6 half-factor discovery**: old random search remains valid but is insufficient; rerun with targeted adversarial falsification.

## Results not invalidated

- V7 fixed-panel development results.
- MASTER RU/RI theorem diagnostics, Gamma-box tightening, held-out calibration from runs unaffected by support-width bug.
- Functional sequential stopping (the sigma model is explicitly known Gaussian in that lab).
- Structural approximate-defect search.
- Dynamic deterministic drift diagnostics.

## Release gate

```bash
python -m compileall -q research_chains scripts envs tests
python -m scripts.run_release_tests -q
```

Expected on audited tree: `289 passed` and process exit code `0`. The wrapper disables ambient third-party pytest plugin autoload; it does not change test collection inside the repository.

## 1. Quick full-chain smoke + automatic fresh analyzer

```bash
python -m scripts.run_high_value_extension_suite \
  --profile quick \
  --seeds 0 \
  --out-root research/high_value_extensions/runs_quick_v3
```

This now writes `DECISION_MATRIX_AUTO.json` after the suite completes, preventing stale decision matrices.

## 2. Fresh 5-seed screening

```bash
python -m scripts.run_high_value_extension_suite \
  --profile screening \
  --seeds 0 1 2 3 4 \
  --out-root research/high_value_extensions/runs_screening_v3
```

Use the auto-generated:

```text
research/high_value_extensions/runs_screening_v3/DECISION_MATRIX_AUTO.json
```

## 3. MASTER rerun

```bash
python -m scripts.run_master_extension_lab \
  --instances 1000 \
  --budgets 16 32 64 128 256 \
  --seed 100 \
  --tolerance 0.05 \
  --out research/high_value_extensions/master/deep_seed100_v3.json
```

Check:
- `support_uncertainty.nonzero_width_fraction > 0.9`
- `active_acquisition.uncertainty_targeted`
- randomized vs balanced-targeted vs uncertainty-targeted separately
- `cascade.frontier` and false-safe counts
- do not call balanced `targeted` uncertainty-adaptive.

## 4. Functional matched-budget rerun

```bash
python -m scripts.run_query_optimal_allocation_lab \
  --instances 1000 \
  --seeds 100 101 102 103 104 \
  --budgets 16 32 64 128 256 \
  --relations 5 \
  --actions 6 \
  --topk 2 \
  --out research/high_value_extensions/functional/allocation_deep_v2.json
```

Use `endpoint_winners` for deployable methods. `endpoint_winners_all` includes oracle/known-sigma diagnostics.

## 5. D6 deep + adversarial half-factor falsification

```bash
python -m scripts.run_d6_extension_lab \
  --instances 10000 \
  --sharpness-instances 100000 \
  --adversarial-instances 2000 \
  --adversarial-steps 40 \
  --seed 100 \
  --out research/high_value_extensions/d6/deep_seed100_v2.json
```

The proposed `(m-1)*delta_square/2` bound remains a conjecture unless formally proved; one adversarial counterexample kills it immediately.

## 6. Omni full-joint D6 stress

Start with 3 sources:

```bash
python -m scripts.run_omni_d6_full_joint \
  --seed 3001 \
  --m-sources 3 \
  --n-states 4 \
  --warmup-steps 3 \
  --out research/high_value_extensions/d6/omni_full_joint_seed3001.json
```

Then repeat seeds 3002--3005 if runtime is acceptable. This is full-Cartesian Omni command evidence only; it is not coupled-support evidence.

## 7. Query deep rerun

```bash
python -m scripts.run_query_extension_lab \
  --instances 10000 \
  --seed 100 \
  --n-rel 12 \
  --k 3 \
  --out research/high_value_extensions/query/deep_seed100_v2.json
```

Report aligned and `cross_query_entangled` native-query advantage separately. Neither substitutes for external MARL/XAI baselines.

## 8. Structural / Dynamic

No code bug invalidated the prior deep results. Do not rerun unless increasing falsification depth or adding external evidence.
# CIG-AMF post-results + 100-track audit rerun guide

This patch is cumulative against `MARL-EXP-main (3).zip`: it includes the 100-track audit hardening plus the result-driven fixes discovered after the first deep runs.

## Results invalidated and must be rerun

1. **MASTER deep support-uncertainty**: old run had `mean_span_interval_width=0`; generator was vacuous.
2. **Functional matched-budget allocation**: old `C_successive_elimination` used true synthetic sigma, and headline winners could include oracle strategies.
3. **Query deep synthetic transfer**: keep old aligned result as development evidence, but rerun with the new `cross_query_entangled` stress family.
4. **D6 half-factor discovery**: old random search remains valid but is insufficient; rerun with targeted adversarial falsification.

## Results not invalidated

- V7 fixed-panel development results.
- MASTER RU/RI theorem diagnostics, Gamma-box tightening, held-out calibration from runs unaffected by support-width bug.
- Functional sequential stopping (the sigma model is explicitly known Gaussian in that lab).
- Structural approximate-defect search.
- Dynamic deterministic drift diagnostics.

## Release gate

```bash
python -m compileall -q research_chains scripts envs tests
python -m scripts.run_release_tests -q
```

Expected on audited tree: `289 passed` and process exit code `0`. The wrapper disables ambient third-party pytest plugin autoload; it does not change test collection inside the repository.

## 1. Quick full-chain smoke + automatic fresh analyzer

```bash
python -m scripts.run_high_value_extension_suite \
  --profile quick \
  --seeds 0 \
  --out-root research/high_value_extensions/runs_quick_v3
```

This now writes `DECISION_MATRIX_AUTO.json` after the suite completes, preventing stale decision matrices.

## 2. Fresh 5-seed screening

```bash
python -m scripts.run_high_value_extension_suite \
  --profile screening \
  --seeds 0 1 2 3 4 \
  --out-root research/high_value_extensions/runs_screening_v3
```

Use the auto-generated:

```text
research/high_value_extensions/runs_screening_v3/DECISION_MATRIX_AUTO.json
```

## 3. MASTER rerun

```bash
python -m scripts.run_master_extension_lab \
  --instances 1000 \
  --budgets 16 32 64 128 256 \
  --seed 100 \
  --tolerance 0.05 \
  --out research/high_value_extensions/master/deep_seed100_v3.json
```

Check:
- `support_uncertainty.nonzero_width_fraction > 0.9`
- `active_acquisition.uncertainty_targeted`
- randomized vs balanced-targeted vs uncertainty-targeted separately
- `cascade.frontier` and false-safe counts
- do not call balanced `targeted` uncertainty-adaptive.

## 4. Functional matched-budget rerun

```bash
python -m scripts.run_query_optimal_allocation_lab \
  --instances 1000 \
  --seeds 100 101 102 103 104 \
  --budgets 16 32 64 128 256 \
  --relations 5 \
  --actions 6 \
  --topk 2 \
  --out research/high_value_extensions/functional/allocation_deep_v2.json
```

Use `endpoint_winners` for deployable methods. `endpoint_winners_all` includes oracle/known-sigma diagnostics.

## 5. D6 deep + adversarial half-factor falsification

```bash
python -m scripts.run_d6_extension_lab \
  --instances 10000 \
  --sharpness-instances 100000 \
  --adversarial-instances 2000 \
  --adversarial-steps 40 \
  --seed 100 \
  --out research/high_value_extensions/d6/deep_seed100_v2.json
```

The proposed `(m-1)*delta_square/2` bound remains a conjecture unless formally proved; one adversarial counterexample kills it immediately.

## 6. Omni full-joint D6 stress

Start with 3 sources:

```bash
python -m scripts.run_omni_d6_full_joint \
  --seed 3001 \
  --m-sources 3 \
  --n-states 4 \
  --warmup-steps 3 \
  --out research/high_value_extensions/d6/omni_full_joint_seed3001.json
```

Then repeat seeds 3002--3005 if runtime is acceptable. This is full-Cartesian Omni command evidence only; it is not coupled-support evidence.

## 7. Query deep rerun

```bash
python -m scripts.run_query_extension_lab \
  --instances 10000 \
  --seed 100 \
  --n-rel 12 \
  --k 3 \
  --out research/high_value_extensions/query/deep_seed100_v2.json
```

Report aligned and `cross_query_entangled` native-query advantage separately. Neither substitutes for external MARL/XAI baselines.

## 8. Structural / Dynamic

No code bug invalidated the prior deep results. Do not rerun unless increasing falsification depth or adding external evidence.
# CIG-AMF post-results + 100-track audit rerun guide

This patch is cumulative against `MARL-EXP-main (3).zip`: it includes the 100-track audit hardening plus the result-driven fixes discovered after the first deep runs.

## Results invalidated and must be rerun

1. **MASTER deep support-uncertainty**: old run had `mean_span_interval_width=0`; generator was vacuous.
2. **Functional matched-budget allocation**: old `C_successive_elimination` used true synthetic sigma, and headline winners could include oracle strategies.
3. **Query deep synthetic transfer**: keep old aligned result as development evidence, but rerun with the new `cross_query_entangled` stress family.
4. **D6 half-factor discovery**: old random search remains valid but is insufficient; rerun with targeted adversarial falsification.

## Results not invalidated

- V7 fixed-panel development results.
- MASTER RU/RI theorem diagnostics, Gamma-box tightening, held-out calibration from runs unaffected by support-width bug.
- Functional sequential stopping (the sigma model is explicitly known Gaussian in that lab).
- Structural approximate-defect search.
- Dynamic deterministic drift diagnostics.

## Release gate

```bash
python -m compileall -q research_chains scripts envs tests
python -m scripts.run_release_tests -q
```

Expected on audited tree: `289 passed` and process exit code `0`. The wrapper disables ambient third-party pytest plugin autoload; it does not change test collection inside the repository.

## 1. Quick full-chain smoke + automatic fresh analyzer

```bash
python -m scripts.run_high_value_extension_suite \
  --profile quick \
  --seeds 0 \
  --out-root research/high_value_extensions/runs_quick_v3
```

This now writes `DECISION_MATRIX_AUTO.json` after the suite completes, preventing stale decision matrices.

## 2. Fresh 5-seed screening

```bash
python -m scripts.run_high_value_extension_suite \
  --profile screening \
  --seeds 0 1 2 3 4 \
  --out-root research/high_value_extensions/runs_screening_v3
```

Use the auto-generated:

```text
research/high_value_extensions/runs_screening_v3/DECISION_MATRIX_AUTO.json
```

## 3. MASTER rerun

```bash
python -m scripts.run_master_extension_lab \
  --instances 1000 \
  --budgets 16 32 64 128 256 \
  --seed 100 \
  --tolerance 0.05 \
  --out research/high_value_extensions/master/deep_seed100_v3.json
```

Check:
- `support_uncertainty.nonzero_width_fraction > 0.9`
- `active_acquisition.uncertainty_targeted`
- randomized vs balanced-targeted vs uncertainty-targeted separately
- `cascade.frontier` and false-safe counts
- do not call balanced `targeted` uncertainty-adaptive.

## 4. Functional matched-budget rerun

```bash
python -m scripts.run_query_optimal_allocation_lab \
  --instances 1000 \
  --seeds 100 101 102 103 104 \
  --budgets 16 32 64 128 256 \
  --relations 5 \
  --actions 6 \
  --topk 2 \
  --out research/high_value_extensions/functional/allocation_deep_v2.json
```

Use `endpoint_winners` for deployable methods. `endpoint_winners_all` includes oracle/known-sigma diagnostics.

## 5. D6 deep + adversarial half-factor falsification

```bash
python -m scripts.run_d6_extension_lab \
  --instances 10000 \
  --sharpness-instances 100000 \
  --adversarial-instances 2000 \
  --adversarial-steps 40 \
  --seed 100 \
  --out research/high_value_extensions/d6/deep_seed100_v2.json
```

The proposed `(m-1)*delta_square/2` bound remains a conjecture unless formally proved; one adversarial counterexample kills it immediately.

## 6. Omni full-joint D6 stress

Start with 3 sources:

```bash
python -m scripts.run_omni_d6_full_joint \
  --seed 3001 \
  --m-sources 3 \
  --n-states 4 \
  --warmup-steps 3 \
  --out research/high_value_extensions/d6/omni_full_joint_seed3001.json
```

Then repeat seeds 3002--3005 if runtime is acceptable. This is full-Cartesian Omni command evidence only; it is not coupled-support evidence.

## 7. Query deep rerun

```bash
python -m scripts.run_query_extension_lab \
  --instances 10000 \
  --seed 100 \
  --n-rel 12 \
  --k 3 \
  --out research/high_value_extensions/query/deep_seed100_v2.json
```

Report aligned and `cross_query_entangled` native-query advantage separately. Neither substitutes for external MARL/XAI baselines.

## 8. Structural / Dynamic

No code bug invalidated the prior deep results. Do not rerun unless increasing falsification depth or adding external evidence.
