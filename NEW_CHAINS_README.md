# CIG-AMF New-Chain Research Harness (v2)

This refactor adds a typed, fail-closed research layer for the surviving equation chains without deleting the historical H1/P01/P06/Paper-B code.

## New shared package

`research_chains/` contains reusable abstractions rather than paper-specific runners:

- `contracts.py` — typed estimand/history/reference semantics and certificate levels.
- `support.py` — exact finite supports and `Omega^- subset Omega subset Omega^+` brackets.
- `finite_world.py` — additive and near-additive finite response worlds.
- `certificates.py` — exact radius, deficit identity, one-sided zeta/2, E/2, LP lower bound, gauge-invariant `delta_circ`, support brackets.
- `reference.py` — general conditional `kappa`, isolation deviation `chi`, residual deviation `rho`, TV bound, product-reference surrogate and finite universal-reference-fidelity characterization.
- `pairwise.py` — sharp and operational score-to-decision certificates.
- `functionals.py` — C/D functionals, extrema gaps, split C, simultaneous C intervals and floor-constrained D allocation.
- `estimation.py` — explicit natural/frozen/transported history-standardization contracts.
- `oracle.py` — clone-state MARL joint-response/support adapter.
- `f3.py` — generic paired shadow learner interface for moving-estimand experiments.
- `provenance.py` — typed fingerprints and fail-closed development manifest helpers.

## New experiment entry points

```bash
# Cheap aggregate blockers
python -m scripts.run_new_chain_suite --quick

# B/H: support geometry, E/2, zeta_def/2, LP, support brackets
python -m scripts.run_chain_bh_lab --instances 1000 --out research/new_chains_v2/chain_bh/summary.json

# R_iso + rho + PAIRWISE operational transfer
python -m scripts.run_chain_rp_lab --instances 1000 --out research/new_chains_v2/chain_rp/summary.json

# A: C-vs-D regularity + simultaneous/split C + matched-budget D allocation
python -m scripts.run_chain_a_functional_lab --replicates 3000 --out research/new_chains_v2/chain_a/summary.json

# Structural rankability discovery; exhaustive for m=3 binary worlds
python -m scripts.run_chain_structural_search --mode exhaustive3 --out research/new_chains_v2/structural/summary.json

# Reference-fidelity theorem discovery/falsification
python -m scripts.run_chain_reference_fidelity_search --instances 5000 --out research/new_chains_v2/reference_fidelity/summary.json

# Primitive-world query semantics
python -m scripts.run_chain_e_semantic_lab --out research/new_chains_v2/chain_e/summary.json

# F3 moving-estimand plumbing only
python -m scripts.run_chain_f3_shadow_smoke --out research/new_chains_v2/chain_f3/summary.json

# Actual OmniArena clone-state environment -> finite joint-response bridge
python -m scripts.run_chain_oracle_bridge_omni --seed 17 --out research/new_chains_v2/oracle_bridge_omni/summary.json
```

## Important semantics

1. `R_iso` and `R_feas` are not interchangeable. `chi` is an isolation error only when the target is a primitive isolated component.
2. Product-reference Paper-13 surrogate and primitive-isolation routes remain separate.
3. The existing `CrossFittedConditionalAIPW` now fails closed if asked to represent arbitrary frozen/transported `nu*`; it explicitly targets natural `P(W|X)`.
4. Missing/not-fitted H1 metrics are `None`/unavailable rather than scientific zero.
5. `dr_exercised` now means DR was actually requested and applied. `dr_integrity_gate_pass` retains the correct process logic for plugin arms.
6. All new runners are development-only. They do not open confirmatory seeds.
7. Omni clone-state support is typed as `Omega_nominal`, `Omega_valid`, `Omega_requestable`, and `Omega_honored`. Do not infer joint-support coupling from an action request mismatch alone.
8. `OmniArena.last_actions` is a mapping keyed by agent id. The oracle normalizes mapping/sequence execution telemetry before comparing requests to executed commands; dictionary-key iteration is never treated as an action vector.
9. Omni command support is distinct from state-effect realization: a movement command may be honored while collision/grid physics prevents displacement.

## What is and is not ready

The code can now falsify all main deterministic/synthetic chain mathematics through a common finite-world API and can bridge clone-state MARL environments into joint response tables.

Remaining scientific adapters are intentionally not faked:

- no Lean/lake is present in this runtime, so B4-B9/H/R/P are not freshly Lean-verified;
- a learned CIG-AMF shadow-learner adapter is still needed before F3 can be called learned-policy evidence;
- construction of statistically certified `Omega^- / Omega^+` from logged MARL data is a research/statistical task, not inferred from observed tuples;
- high-probability `delta_circ`, `eta`, `rho`, and support bounds need estimator-specific coverage methods before an oracle bound becomes a deployed certificate;
- arbitrary transported AIPW is not implemented; use direct frozen standardization of history-level `mu` unless a transport ratio is added and validated.
