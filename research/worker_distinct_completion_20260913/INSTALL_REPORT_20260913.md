# Batch R (five new packages) — brought into cig-amf-main

The R-batch had been built in a separate checkout
(`~/Documents/ChatGPT/CIG-AMF/work/distinct_completion_20260913`) and, unlike the
earlier batches, had no `install.py`/`finalize.py`. Its modules were therefore
absent from `cig-amf-main`. They are now installed.

## What was installed and how

The 13 batch modules were copied as SOURCE and **recompiled in place** with
`scripts/compile_receipt_v2.py`. The `.olean` files were deliberately not copied:
the repository's acceptance rule requires `lean_exit = 0`, unchanged source hash,
an `.olean` strictly newer than its source, and an axiom audit parsed from a log
produced by that same run. A binary carried over from another checkout satisfies
none of the mtime/log conditions, so copying it would have produced an
unverifiable "acceptance".

All 70 modules in the batch's `dependencies/` directory already existed in
`cig-amf-main`; nothing was missing.

| module | audits |
|---|---:|
| LeanD6ApproximateActualEvaluatorV1 | 3 |
| LeanD6WidthCostInformationV1 | 3 |
| LeanD6ScalarWidthRegionV1 | 4 |
| LeanFunctionalContrastDesignV1 | 5 |
| LeanFunctionalContrastInfimumV1 | 3 |
| LeanFunctionalContrastPotentialV1 (new, this session) | 5 |
| LeanFunctionalOneCellInformationV1 | 6 |
| LeanQueryCriticalResolutionV1 | 5 |
| LeanStructuralBudgetRecourseV1 | 5 |
| LeanStructuralRandomMenuExactV1 | 4 |
| LeanSupportIntervalHittingV1 | 2 |
| LeanSupportCyclicWindowV1 | 5 |
| LeanSupportNonadaptiveLowerV1 | 2 |
| LeanSupportNonadaptiveExactV1 | 5 |

**14 modules, 57 audits, every one `{propext, Classical.choice, Quot.sound}`,
0 failures.**

Also copied here: the three proof notes, `SCOPE_SOURCES.json`, the four probe
artifacts with their generators (`fixed_epsilon_recourse`, `parity_bundle_probe`,
`width_cost_game`, `passive_dense_moments`), the batch's 17 original compile logs
(under `logs/`), and `aux/CurrentRepoAxiomAudit.lean`. The three probe generators
are also at `scripts/R_*.py`.

## Audit of the two outside checkouts

Asked for explicitly, so recorded here. `~/Documents/ChatGPT/CIG-AMF`: 336 Lean
files, 331 `.olean`, **no `sorryAx` and no compile error anywhere**. Three logs
match a naive grep for "error" — `LeanD6FiniteSolverToleranceV1`,
`LeanFiniteGridSolverV1`, `LeanQueryResolutionMinimaxV1` — but in all three the
word occurs only inside a theorem NAME (`resolution_error`, `solve_error`,
`midpoint_error`) and the axiom lines are clean. `~/Documents/Codex` contains no
project Lean source at all, only a Mathlib/aesop toolchain checkout. After this
install the only project file in either checkout that is not in `cig-amf-main` is
`work/lean/CurrentRepoAxiomAudit.lean`, which is copied to `aux/` here.

## New this session: `LeanFunctionalContrastPotentialV1`

`CONTRAST_DESIGN_PROOF.md` recorded the connected effective-resistance theorem as
the open item of R1. This module closes the gap with two certificates, so the
Laplacian pseudoinverse is never needed in the kernel of the argument:

* `potential_upper` — any potential `p` with `p a - p b > 0`, rescaled, is an
  admissible alternative of energy `delta^2 E_c(p)/(p a - p b)^2`. Minimising
  over `p` is the Dirichlet form of `R_eff`: the upper half.
* `flow_green` — the discrete Green identity: a unit flow from `a` to `b` reads
  off `z a - z b`, by antisymmetry plus the divergence condition.
* `flow_lower`, `flow_lower_div` — Cauchy-Schwarz against any unit flow:
  `delta^2 <= 2 * flowResistance c f * contrastEnergy c z`. Thomson's principle
  says the best flow attains `R_eff`: the lower half.

A potential and a flow whose values agree therefore constitute a complete proof
of `J_c` for that graph.

### What this does NOT establish

- That the two optima meet — `min over p = 1/(2 R_eff) = max over f` — is
  Dirichlet/Thomson duality and is **not** proved. Without it these are two
  bounds, not the formula `J_c = delta^2/(2 max R_eff)`.
- The maximisation over pairs `(a,b)` is not formalised.
- Star and path rows of the topology table remain certified **numerically only**
  (the exact `Fraction` probe at `K = 3,4,6,8,12`), not in Lean.
- Nothing here addresses the optimal topology when the extrema are unknown, nor
  distance-dependent edge costs `kappa_ab = 1 + l|a-b|`.
- `flow_lower` assumes the flow is supported on positive-conductance edges
  (`c i j = 0 -> f i j = 0`) and `c >= 0`.

## Still open in batch R

- **R1**: Dirichlet/Thomson duality; star/path in Lean; unknown-extrema topology
  design (Laplacian QP); distance-dependent edge costs.
- **R2**: the region `mu < 1/2` is not characterised — the numerical grid shows
  width-two optima there and mixed-width optima near `z = 1`, which are
  observations, not theorems. The scalar-only optimality theorem covers
  `mu >= 1/2` only.
- **R3**: the fixed-`epsilon` question (is `R_eps` uniformly bounded, or does it
  grow?) beyond the staircase family.
- **R4**: the positive condition — decision-relevant mass weaker than a minimum
  mass on every support point.
- **R5**: a positive bundle-size theorem; the current result is the budget cliff
  `min(d, M)` plus greedy negative controls.
