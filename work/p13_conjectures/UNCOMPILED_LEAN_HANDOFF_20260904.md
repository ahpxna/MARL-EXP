# Uncompiled Lean handoff — 2026-09-04

Every file below was written WITHOUT a Lean toolchain available (no `lake`,
`lean`, `elan` reachable from the authoring shell).  Status for all of them is
therefore **SOURCE WRITTEN, NOT COMPILED** — not `COMPILED ARTIFACT`, and
certainly not `PROVED`.  All are zero-`sorry` by grep.  Nothing here may be
cited as evidence until `lake env lean -o <file>.olean <file>.lean` exits clean and the log is
recorded in `compile_logs/`.


## BUILD COMMAND — read this before compiling anything

`lake env lean File.lean` only TYPE-CHECKS.  It exits 0 and prints nothing, but
it writes no `.olean`, so the next module that imports it fails with
`unknown module prefix`.  Always pass `-o`:

```
cd work/p13_conjectures
lake env lean -o Module.olean Module.lean
```

This matches the repo's own build scripts (`compile_logs/run_high_value_build.sh`
uses `"$LEAN" -o "$module.olean" "$module.lean"`).

`work/p13_conjectures` is a FLATTENED copy of `work/p12` plus the p13 modules:
imports are resolved by filename in that one directory, not by package path.  A
module imported from p12 must be copied in (both `.lean` and `.olean`) before it
resolves.  18 such modules were copied on 2026-09-05.

Compile from this directory:

```
cd work/p13_conjectures
lake env lean -o LeanStructuralStaircaseExactPrefixCoverV1.olean LeanStructuralStaircaseExactPrefixCoverV1.lean
lake env lean -o LeanD6RankOneLocalAffineSliceV1.olean LeanD6RankOneLocalAffineSliceV1.lean
lake env lean -o LeanD6RankOneTwoCornerInterpolationV1.olean LeanD6RankOneTwoCornerInterpolationV1.lean
lake env lean -o LeanD6RankOneReferenceInvarianceV1.olean LeanD6RankOneReferenceInvarianceV1.lean
lake env lean -o LeanD6ScalarMultiaffineRankOneV1.olean LeanD6ScalarMultiaffineRankOneV1.lean
lake env lean -o LeanD6ProfileFibreAdditiveSteeringV1.olean LeanD6ProfileFibreAdditiveSteeringV1.lean
lake env lean -o LeanD6StrictRankOneM6WitnessV1.olean LeanD6StrictRankOneM6WitnessV1.lean
lake env lean -o LeanD6StrictRankOneM6ResponseSpansV1.olean LeanD6StrictRankOneM6ResponseSpansV1.lean
lake env lean -o LeanD6StrictRankOneM6StrictTopCV1.olean LeanD6StrictRankOneM6StrictTopCV1.lean
```

## 1. LeanStructuralStaircaseExactPrefixCoverV1.lean  (690 lines, +221 new)

Completes the UPPER branch of the staircase prefix-cover dimension, giving the
exact law `chi_prefix(F_r, 0) = r = m/2`.

New declarations: `staircaseSelected_card`, `staircaseSelected_exact_optimal`,
`lowChain`, `lowChain_inclusionChain`, `lowRanking_exists`,
`blockRanking_exists`, `lowRanking`, `blockRanking`, `stairMenuFun`,
`stairMenu`, `stairMenu_card_le`, `stairMenu_prefixCover`,
`STRUCT_staircase_prefix_cover_at_most_r`,
`STRUCT_staircase_prefix_dimension_eq`,
`STRUCT_staircase_chi_eq_half_ground_set`.

Menu size is `r`, not `r+1`, because the low chain already covers layer `r-1`,
so the last index is reused for it rather than for a block ranking.

Pre-compile evidence: construction verified by exact enumeration for
r = 1,2,3,4 (every cardinality layer covered, menu size exactly r).  Exact
DP+MILP agreement at r = 7 is in `research/structural/staircase_exact_r7_20260904.json`.

Likely first-compile failure points: `Finset.card_compl` / `Finset.eq_univ_of_card`
name or shape; `simpa [kk]` where a `Fin` coercion `kk.val = k` must be seen
through (may need an explicit `show`); `subst hHigh` in the `k = 2r-1` branch.

## 2. LeanD6RankOneLocalAffineSliceV1.lean  (86 lines)  — D6-R1

`interactionContrastRankOne_local_affine_slice` plus its converse and the
packaged iff.  Pure rearrangement of the factorization predicate.

## 3. LeanD6RankOneTwoCornerInterpolationV1.lean  (101 lines)  — D6-R2a core

`interactionContrastRankOne_pivot_profile` (every profile is a scalar multiple
of ONE pivot profile — this eliminates the abstract factor `h` entirely),
the world-level unfolded form, and the Bernstein-seed affine restatement.
Degenerate branch (`lambda` identically zero) takes `v := u0`, `phi := 0`.

Highest-risk step: `rw [..., ← mul_assoc, hcancel]` in the pivot lemma;
fallback is `field_simp` on that `have`.

## 4. LeanD6RankOneReferenceInvarianceV1.lean  (168 lines)  — NEW RESULT

The D6 rank-one class does not depend on the product reference.

`productResponse_contrast_eq_productExpectation`,
`productExpectation_congr`, `productExpectation_const_add_smul`,
`interactionContrastRankOne_reference_transfer`,
`interactionContrastRankOne_reference_free`,
`allCoordinatesInteractionContrastRankOne_reference_transfer`,
`allCoordinatesInteractionContrastRankOne_reference_free`,
`allInteractionContrastProfileMinorsZero_reference_transfer`.

The only hypothesis is normalization of the target reference
(`sum_c jointWeight q' c = 1`) — NO strict positivity, so deterministic
point-mass references are covered.  The transfer keeps the action factor
`lambda` IDENTICAL and only recentres the context factor `h`.

Consequence for the raw-world search: the linear rank-one fibre is
reference-free, so one nullspace serves every reference; only the decision
objective changes with the reference.

Pre-compile evidence (exact rational, `research`-side script, not committed):
48 worlds at (m,K) = (3,3), (4,3), (3,4), (5,3), each tested against 14
normalized references (uniform, point-mass, 6 deterministic corners, 6 generic).
Rank-one verdict invariant in 48/48; `lambda` identical across all references
in 48/48; `h` differed by a constant in 48/48; 0/24 generic worlds accidentally
rank-one (gate non-vacuous).

## 5. LeanD6ScalarMultiaffineRankOneV1.lean  (202 lines)  — NEW RESULT

SUFFICIENCY half of the D6 normal-form question.  `scalarMultiaffineWorld`
(coordinate-additive part plus a tensor core in scalar latent maps `phi`, full
powerset) and `multiaffineContextFactor` (the coordinate-`i` cofactor), with:
`scalarMultiaffineWorld_slice_contrast`,
`scalarMultiaffineWorld_interactionContrastRankOne`,
`scalarMultiaffineWorld_allCoordinatesInteractionContrastRankOne`,
`scalarMultiaffineWorld_allMinorsZero`.

The witness is explicit: `lambda u = phi i u - phi i u0` and
`h z = H_i z - E_q H_i`.

**The CONVERSE is not proved and is not asserted anywhere in the file.**
Rank one at every coordinate implying this normal form remains open; the
current evidence for it is computational only (an exact fibre-dimension
identity at m = 4).

Pre-compile evidence (exact rational): slice-contrast identity 23024/23024
exact across (m,K) = (3,3), (4,3), (3,4), (4,2), (5,3); `rank_one_check` True
at 200/200 (world, reference) pairs; the explicit witness identity
`psi_{i,u}(z) = lambda(u) * (H_i(z) - E_q H_i)` held with 0 violations.
