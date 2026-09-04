# New Priority Branch Status — 2026-09-02

Pinned environment: Lean `4.34.0-rc2`; Mathlib `1f495c611d05d2215058cd77c7897d625bc3b445`.

This branch adds extension modules only. Frozen P12 statements and legacy P13 routes were not edited by this batch.

## Compiled results

| Priority | Module | Result | Status |
|---|---|---|---|
| Structural characterization | `LeanStructuralOrdinaryChainCharacterizationV1` | Defines ranking-free inclusion-chain covers, proves every finite inclusion chain extends to one full ranking, and proves the exact layer-transversal/inclusion-chain-cover characterization of prefix-cover dimension. | COMPILED ZERO-SORRY |
| D6 active cells | `LeanD6PolyhedralActiveCellV1` | Defines an explicit finite linear-inequality predicate and proves equivalence with the existing active decision-cell validity predicate. | COMPILED ZERO-SORRY |
| D6 certificate language | `LeanD6CanonicalUniformDecisionCertificateV1` | Restricts certificates to mixed-difference atoms and canonical active-cell constraint atoms with nonnegative multipliers; proves soundness. | COMPILED ZERO-SORRY |
| D6 finite cells | `LeanD6CanonicalPolyhedralCellsV1` | Supplies exact canonical Fin4 and Fin6 certificates of mass 3 and 5 and derives the corresponding decision-interaction upper bounds. | COMPILED ZERO-SORRY |
| D6 Fin6 primal saturation | `LeanD6Fin6GammaFiveSaturationV1` | Formalizes the exact 64-entry rational world for selected `{1,2,3}` and competitor `{0,4,5}`; proves normalized point-mass reference, unit mixed-difference bound, response spans one, valid balanced Top-3 active cell, losses `3` and `1/2`, doubled gap `5`, and impossibility of any uniform constant below five for this cell. | COMPILED ZERO-SORRY |
| D6 Fin6 exact weighted dual | `LeanD6Fin6WeightedDualCertificateV1` | Encodes the authoritative six-cycle coefficients with absolute masses `1/2,1/2,1,3/2,1/2,1`, seven canonical active-cell multipliers, proves the exact functional identity and mass five, then combines primal and dual results to identify the cell's exact uniform constant. | COMPILED ZERO-SORRY |
| D6 normalization audit | `LeanD6BalancedLawCounterexampleV1` | Gives an exact balanced `m=2` cell showing that the legacy `BalancedDecisionInteractionBound` (which omitted `hWeight/hNorm`) is false: an additive world has zero mixed differences but doubled decision gap `2 > m-1`.  It also proves the reference joint mass is `4`, isolating the missing normalization rather than refuting the normalized scientific target. | COMPILED ZERO-SORRY |
| D6 corrected target | `LeanD6NormalizedBalancedTargetV1` | Defines the nonnegative normalized balanced-cell statement and proves it is equivalent to the normalized all-cell law, using the already-closed non-balanced theorem. | COMPILED ZERO-SORRY |
| D6 active-cell cone decomposition | `LeanD6CanonicalPathRemainderV1`, `LeanD6ActiveCellRemainderDecompositionV1` | Exposes the mixed-difference part and canonical active-cell remainder of a supplied restricted certificate; proves the remainder is exactly a nonnegative canonical-constraint combination and is nonpositive on every valid active cell.  It does not assert existence for arbitrary balanced cells. | COMPILED ZERO-SORRY |
| D6 active-cell completion bridge | `LeanD6ActiveCellCompletionV1` | Defines actual canonical completion at a mass bound, proves completion implies the decision-interaction bound, and proves that universal normalized balanced completion would close the normalized balanced law.  Instantiates the bridge for the exact Fin4 and Gamma-five Fin6 cells. | COMPILED ZERO-SORRY / UNIVERSAL EXISTENCE OPEN |
| Structural hard witness | `LeanStructuralActualChi4WitnessV1` | Gives an actual `selectedRadius`/supportOsc instance on six relations whose four unique nontrivial budget optima form an inclusion antichain; proves prefix-cover dimension is not at most 3. | COMPILED ZERO-SORRY |
| Structural stronger hard witness | `LeanStructuralScalarChi5WitnessV1` | Gives an actual two-support-point `selectedRadius`/supportOsc instance on seven relations whose five forced unique budget optima are pairwise incomparable; proves prefix-cover dimension is not at most 4. | COMPILED ZERO-SORRY |
| Structural unbounded family | `LeanStructuralStaircaseFamilyV1`, `LeanStructuralStaircaseUnboundedV1`, `LeanStructuralUnboundedPrefixCoverFamilyV1` | Constructs actual finite component functions with positive basis relations and negative staircase relations; characterizes every zero-radius omitted set; proves that for every `r > 0`, fewer than `r` rankings cannot cover all zero-tolerance budget layers.  Thus `chi_prefix(F_r,0) >= r`. | COMPILED ZERO-SORRY |
| Structural universal upper bound | `LeanStructuralPrefixCoverUniversalUpperV1` | For every finite objective on `I`, constructs one exact-optimum ranking per budget and proves a prefix-cover menu of size at most `|I|+1`; combines this with the staircase family into `r <= chi_prefix(F_r,0) <= 2r+1`.  The explicit `r=6` corollary is on 12 relations, not Fin 8. | COMPILED ZERO-SORRY |
| MASTER/TCC | `LeanTypedObstructionIndispensabilityCalculusV1` | Builds a direct-product obstruction calculus and instantiates it with the exact response, reference, support, interaction, and query witnesses; proves each evidence type is individually indispensable in the joint five-type instance. | COMPILED ZERO-SORRY |

## Honest open boundaries

- The earlier canonical Fin4/Fin6 certificates are upper bounds.  For the new authoritative Fin6 LP cell specifically, the exact primal saturation plus weighted dual certificate proves that five is the minimal valid uniform constant.  Fin4 minimality and the universal balanced-cell theorem remain open.
- The new cone-completion files classify the remainder of every *supplied* canonical certificate and close its soundness bridge.  They do not construct a mass-`n` certificate for every normalized balanced cell; `NormalizedBalancedDecisionInteractionBound` therefore remains open.
- The literal unnormalised legacy `BalancedDecisionInteractionBound.{0}` is now formally falsified.  The scientifically intended balanced law under nonnegative normalized product weights, and hence the normalized universal D6 half-factor theorem, remain open.
- The actual supportOsc prefix-cover dimension is now formally unbounded: the staircase family proves `chi_prefix(F_r,0) >= r` for every positive `r`.  Equality and an exact closed form for positive tolerance remain open.
- There is no Fin-8/`chi_prefix >= 6` Lean witness in this branch.  The compiled parametric staircase theorem gives `chi_prefix >= 6` at `StairRel 6`, whose ground-set cardinality is 12.  No stronger finite claim is inferred.
- No unrestricted arbitrary-constraint certificate mass is defined in the new canonical branch.
- No Abel, martingale, gauge-normalization, or new atomic-norm direction was opened.
- The superseded strict-margin candidate is retained only as a provenance-discrepancy note under `work/p13_conjectures/legacy/`; it is not an active theorem and is not used to falsify the universal route.

## D6 hard gates for the active-cell completion route

1. A normalized balanced LP candidate with `Gamma > m-1` is only a lead until
   its rational data is independently checked and then formalized as an exact
   Lean counterexample. No floating-point result falsifies the theorem.
2. If normalized LP optima remain below the target but their dual morphology
   changes across cells or references, the proof target is a general
   flow/cone completion; it is not legitimate to impose one fixed canonical
   tree.
3. A tree or leaf-removal induction may be promoted only after the same
   support pattern repeats under heterogeneous normalized references through
   dimensions `m = 4, 6, 8, 10`.
4. The D6 law is **not proved** by any bridge, finite certificate, or
   compilation listed above. It becomes proved only when a zero-sorry Lean
   theorem constructs a mass-`m-1` canonical certificate for every normalized
   balanced active cell.

## Verification

Run:

```bash
zsh compile_logs/run_new_priority_batch_20260902.zsh
```

Static source gate:

```bash
rg -n '\\bsorry\\b|\\badmit\\b|^[[:space:]]*axiom\\b' \
  work/p13_conjectures/LeanStructuralOrdinaryChainCharacterizationV1.lean \
  work/p13_conjectures/LeanD6PolyhedralActiveCellV1.lean \
  work/p13_conjectures/LeanD6CanonicalUniformDecisionCertificateV1.lean \
  work/p13_conjectures/LeanD6CanonicalPolyhedralCellsV1.lean \
  work/p13_conjectures/LeanD6Fin6GammaFiveSaturationV1.lean \
  work/p13_conjectures/LeanD6Fin6WeightedDualCertificateV1.lean \
  work/p13_conjectures/LeanD6BalancedLawCounterexampleV1.lean \
  work/p13_conjectures/LeanD6NormalizedBalancedTargetV1.lean \
  work/p13_conjectures/LeanStructuralActualChi4WitnessV1.lean \
  work/p13_conjectures/LeanStructuralScalarChi5WitnessV1.lean \
  work/p13_conjectures/LeanStructuralStaircaseFamilyV1.lean \
  work/p13_conjectures/LeanStructuralStaircaseUnboundedV1.lean \
  work/p13_conjectures/LeanStructuralUnboundedPrefixCoverFamilyV1.lean \
  work/p13_conjectures/LeanTypedObstructionIndispensabilityCalculusV1.lean
```
