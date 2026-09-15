# Focused non-point strict Top-C active-cell LP audit

Status: `NO_COUNTEREXAMPLE_FOUND`; this is development-only falsification
evidence, not a proof of the normalized balanced law.

## Code audit

`research_chains/d6_active_cell_lp.py` implements a finite binary active-cell
LP.  For a frozen cell it enforces binary mixed-difference range at most one,
all residual and response selector inequalities, and selected-versus-rejected
score inequalities.  A positive `topc_margin` strengthens the non-strict Lean
Top-C premise for stress testing.

There are two encodings:

- `pairwise` directly enumerates rectangle constraints and exposes a cycle-dual
  support;
- `range` is a compact primal-equivalent extended formulation, but does not
  expose direct rectangle coefficients.

The LP itself is floating-point HiGHS.  `exact_verify_binary_solution` is an
independent, fail-closed rational reconstruction of a returned primal; it is
not an exact rational LP solver.  In particular, a floating primal that is
within solver tolerance of a selector/interaction face can fail reconstruction
after denominator truncation.  This happened for some m=6/m=8 non-candidates;
they must not be described as exact witnesses.

## Campaigns

All references below are strictly positive product rows and all active LPs use
a required selected-minus-rejected response-span margin of at least the listed
value.

| Artifact | Scope | Result |
| --- | --- | --- |
| `discovery_m4_m6_m8.json` | m=4,6,8; five random rational-grid references per dimension; margin 1/20; closure and elite mutation | Best floating Gamma: 1.024662, 1.182908, 3.392775, versus targets 3, 5, 7. No numerical candidate. m=4 reconstructed exactly; m=6/m=8 are comfortably sub-target but their rationalized primal failed the fail-closed exact check on tiny face errors. |
| `discovery_m10.json` | m=10; two strictly-positive rational-grid references/cell-closure trajectories plus one elite mutation; margin 1/20 | Best Gamma 5.016465 versus target 9; no numerical candidate. The compact m=10 LP is materially slower (the separate minimal diagnostic took about 50.1 seconds), so it was not expanded into a sweep. |
| `nearpoint_transfer.json` | Transfer historical point-mass saturation primals to `q=(.9,.1)^m` and an interior heterogeneous q; m=4,6,8; margin 1/50 | Best Gamma values remain far below m-1: m4 `-0.04/.185114`, m6 `1.093616/1.032519`, m8 `3.951869/2.670768`. No candidate. |
| `direct_dual_m4_m6.json` | Direct-rectangle re-solves for the strongest transfer cells | Dual morphology varies substantially: m4 near-point has 0 active cycles while heterogeneous m4 has 1; m6 near-point has 54 active cycles while heterogeneous m6 has 31. These are optimizer-selected duals, not canonical trees. |

## Consequence

No sampled strictly-positive non-point product-reference cell exceeded
`m - 1`; hence there is no exact rational counterexample to hand off to Lean.
The campaign also gives no evidence for a fixed canonical tree/transport form:
the direct LP dual supports vary materially across q/cell instances.

Coverage is deliberately narrow: binary actions, finitely many frozen active
cells, and no exact LP enumeration.  It cannot establish the universal
balanced law or its sharpness.
