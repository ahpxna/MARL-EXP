# IEEE experiment workflow added by the research-debug patch

This patch deliberately separates theorem discovery, algorithm benchmarks, and
confirmatory evidence.

## D6 active-cell LP discovery

```bash
python scripts/run_d6_active_cell_lp.py \
  --m-values 4 6 8 --restarts 8 --closure-steps 4 \
  --reference-modes uniform point0 \
  --debug --dump-matrices
```

The result records `Gamma(C)`, the target `m-1`, sparse LP primal/dual
residuals, dual rectangle/cycle coefficients, and active cell inequalities.
A repeated `3,5,7` pattern is **development evidence only**.  Any
`Gamma > m-1` is a counterexample candidate and must be rationally
reconstructed before it is sent to Lean.

## Structural three-level implementation

The new `research_chains.kprefix` module provides:

1. exact acceptable-subset -> inclusion-DAG -> coverage-mask set cover, with an
   optional SciPy MILP cross-check;
2. maximum-weight Best-Chain plus greedy COVER-RANK;
3. `KPrefixNet`, whose K Plackett-Luce ranking heads are trained by REINFORCE
   directly against sampled worst-budget regret, an approximation to
   `epsilon_K`.

Run a Tier-A benchmark:

```bash
python scripts/run_kprefix_benchmark.py \
  --m 6 --k-max 4 --train-instances 32 --test-instances 12 \
  --epochs 120 --verify-milp --debug
```

The script plots K against worst-budget regret, mean-budget regret,
inference/solve time, and memory.  It explicitly records policy return as
unavailable in Tier A rather than relabelling an objective proxy as RL return.
Tier B/C adapters should add real policy return.

## Three benchmark tiers

`config/ieee_benchmark_protocol_v1.json` freezes:

* Tier A: exact finite worlds for theorem sanity, sharpness, counterexamples,
  exact oracles and certificate calibration;
* Tier B: standard MARL adapters for scalability/comparability;
* Tier C: Cross Road or another interaction-rich environment for physical
  interactions, drift, V2V, weather, emergencies and intervention semantics.

Tier B/C are fail-closed as `EXTERNAL_ADAPTER_REQUIRED`; this patch does not
pretend those external environments are bundled.

## Confirmatory statistics

The protocol freezes 10 disjoint confirmatory seeds, 95% confidence intervals,
means, medians where appropriate, a fail-closed failed-run policy, and a
mandatory false-safe rate for certificate methods.  Development hyperparameter
search must stay disjoint from confirmatory seeds.

Validate the contract with:

```bash
python scripts/validate_ieee_benchmark_protocol.py
```

## Scientific ablations

The frozen ablations are theorem-facing rather than neural-layer-facing:

* D6: no certificate; fixed pairwise; fixed high order; adaptive without formal
  trigger; certificate-driven adaptive order.
* Structural: K=1; K>1; prefix consistency off/on.
* MASTER: remove reference/support/interaction/score/query-semantic evidence.

## Debug traces

Both new runners accept `--debug`.  They write append-only JSONL traces with
wall-clock stage timing, RSS, exceptions, LP matrix dimensions, KKT/duality
residuals and per-instance K-Prefix diagnostics.  D6 additionally supports
`--dump-matrices` to save sparse `A`, `b`, objective, labels, and frozen active
cell data for exact reproduction of suspicious cells.
