# Fin-4/Fin-6 D6 dual morphology audit

Status: `NO GENERAL LIFTING THEOREM JUSTIFIED`.

This note audits the compiled finite certificates and the authoritative
development LP artifact before any tree, transport, or dimension-induction
claim is promoted. It does not alter the immutable P12 baseline or the open
normalized balanced-cell target.

## Inputs actually checked

* `LeanD6CanonicalPolyhedralCellsV1.lean`: compiled canonical Fin-4 and
  Fin-6 branch certificates.
* `LeanD6Fin6GammaFiveSaturationV1.lean`: compiled exact primal saturation
  cell, with doubled decision gap `5`.
* `LeanD6Fin6WeightedDualCertificateV1.lean`: compiled exact dual for that
  Fin-6 cell, with canonical cycle mass `5`.
* `research/d6_active_cell_lp/discovery.json`: a development-only sampled
  LP search. It is useful for morphology, not a universal proof.

## Exact certificate comparison

| object | active cell | cycle coefficients | active-cell cone support |
| --- | --- | --- | --- |
| canonical Fin-4 | point mass, canonical branch | three `+1` atoms, mass `3` | two Top-C atoms; no residual atom |
| canonical Fin-6 | point mass, canonical branch | five `+1` atoms, mass `5` | three Top-C atoms; no residual atom |
| Gamma-five Fin-6 | point mass, selected `{1,2,3}`, competitor `{0,4,5}` | `1/2, 1/2, 1, 3/2, -1/2, -1`, absolute mass `5` | one competitor-min, two competitor-max, and four Top-C atoms |

The Gamma-five certificate is exact and nontrivial:

```text
2 [L(selected) - L(competitor)] = 5,
delta_square = 1.
```

It proves an equality case for **that one active cell**, not for all balanced
cells.

## Transport graph of the exact Gamma-five certificate

Its nonzero Top-C multipliers are

```text
1 -> 5 : 1/2
2 -> 0 : 1
2 -> 4 : 1
3 -> 5 : 1/2
```

Viewed as a bipartite graph from selected to rejected coordinates, this is a
forest with two components:

```text
0 -- 2 -- 4       1 -- 5 -- 3
```

It is not one spanning tree. More importantly, it has no coordinatewise flow
conservation visible from the Top-C part alone:

```text
selected outflow = (1/2, 2, 1/2)
rejected inflow  = (1, 1, 1).
```

The recorded dual also has three competitor-extremum atoms. A formal
flow-balance identity combining those atoms with the Top-C graph has not been
derived. Thus this finite certificate is evidence for an active-cell
**cone/flow** mechanism, but it does not support a fixed pairing, a fixed
tree, or a leaf-removal recurrence.

## Why Fin-4 -> Fin-6 is not an inductive certificate pattern yet

The canonical Fin-4 and canonical Fin-6 certificates do have masses `3` and
`5`, respectively. However the Gamma-five Fin-6 saturation certificate has
six signed, fractional cycle coefficients and active residual constraints,
whereas the canonical Fin-4 certificate has three positive unit cycles and
only Top-C constraints. These are different dual morphologies.

There is also no `reduce`, `restrict`, `extend`, or embedding relation in the
definition of `ActiveDecisionCell`. Its axioms relate one fixed cell to its
world function; they provide no link between an arbitrary `(2d+2)`-cell and
any `2d`-cell. Consequently, the statement

```text
completion at 2d -> completion at 2d+2
```

is not derivable from the current active-cell axioms. It would require an
explicit, separately proved cell-reduction hypothesis that preserves:

1. product-reference response semantics;
2. selected/competitor extrema;
3. all fixed active residual witnesses;
4. canonical constraint orientation; and
5. mixed-difference normalization.

No such map currently exists in the formal corpus.

## Cross-dimensional development evidence

The sampled LP artifact has direct rectangle duals for point-mass best cells:

| m | observed Gamma | observed cycle mass | morphology |
| --- | ---: | ---: | --- |
| 4 | 3 | 3 | two nonzero cycle constraints, with residual and Top-C atoms |
| 6 | 5 | 5 | six fractional/signed cycle atoms and a two-component Top-C forest |
| 8 | 6 | 6 | six unit cycle atoms, two residual, two response, and two Top-C atoms |

The `m=8` result is not saturation (`6 < 7`) and is explicitly
development-only. It already differs from both Fin-4 and Fin-6 dual
morphology, so it cannot validate a fixed-tree lifting law. There is no
direct-cycle `m=10` artifact in the repository. The present pairwise
rectangle encoding would have

```text
m * 2^(m-1) * (2^(m-1)-1) = 2,616,320
```

cycle rows at `m=10`; the compact range encoding does not expose individual
cycle multipliers. Therefore the required repeated `m=4,6,8,10`,
heterogeneous-reference morphology gate is not met.

## Consequence for the universal law

The following remains open and is not weakened or falsified by this audit:

```text
forall normalized balanced active cells,
  DecisionInteractionConstantAtMost cell (m - 1).
```

What is proved today is only the conditional bridge

```text
HasCanonicalActiveCellCompletionAtMost cell (m - 1)
  -> DecisionInteractionConstantAtMost cell (m - 1),
```

plus exact Fin-4 and Fin-6 instances.

The defensible next theorem is a cell-intrinsic cone construction that
produces canonical constraint multipliers for every balanced cell, or an
exact counterexample to such a construction. A generic dimension-lifting or
fixed-tree theorem should not be attempted until a reduction map and the
multi-dimension morphology gate are both available.
