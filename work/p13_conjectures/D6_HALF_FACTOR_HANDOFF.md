# D6 half-factor handoff

## Status

The original P13 headline theorem is **not yet closed**.  Its one remaining
`sorry` is deliberately retained rather than replaced by a hidden assumption.

The proof has been factored into four logically distinct pieces:

1. `D6H1_true_loss_diff_eq_surrogate_diff_add_transfer` — compiled.
2. `D6H2_surrogate_selected_le_competitor` — compiled, reusing the frozen P12
   `productA_topC_surrogate_optimal` connector.
3. Direct signed pair-transfer inequality H3 — still open, but its first
   signed exchange ingredients now compile in `LeanD6H3Exchange.lean`:
   product-response contrast as an expectation, pointwise contrast error at
   most `delta`, retained-coordinate `delta`-insensitivity, and the finite
   multi-coordinate patch bound.
4. `D6H4_half_factor_from_direct_pair_transfer` — compiled; it constructs the
   finite cardinality minimizer internally and introduces no external
   surrogate-optimality premise.

Source: `LeanD6HalfFactorCore.lean`.

## What was ruled out

The half factor cannot be obtained by applying two independent uniform-world
perturbation inequalities.  That route necessarily loses the factor of two.
Nor is there a valid identity replacing an oscillation directly by an
expectation of signed telescoping terms: extrema (`maxVal`/`minVal`) must be
retained in H3.

The viable target is the same-cardinality signed comparison

```text
transferErr q F selected - transferErr q F competitor <= n * delta / 2
```

using Top-C optimality and the pre-supremum mixed-difference telescoping
identity.

## Sharpness evidence

`LeanD6HalfFactorSharpness.lean` records an exact rational Fin-3/Fin-2 world:

```text
q = point mass at (1,1,0)
F(000..111) = [0,0,2,2,0,0,1,2]
all response spans = 1
selected Top-C singleton = {2} (valid tie)
competitor = {1}
selected loss = 3/2
competitor loss = 1/2
delta_square = 1
regret = 1 = (3-1)*delta_square/2
```

Thus the proposed coefficient is exactly attained under the current non-strict
Top-K semantics; an asymptotic construction is not needed for sharpness.  The
source proof was written, but its exhaustive finite mixed-difference check was
still compiling when the handoff was requested, so it is correctly labelled
`PROOF_WRITTEN_UNCOMPILED` rather than verified.

A second exact rational witness is sharper for **H3-old itself**:

```text
q = point mass at (0,1,0)
F(000..111) = [-3,-3,-2,-1,0,0,2,2]
selected Top-C singleton = {0}, with strict score margin 3
competitor = {1}
delta_square = 1
T(selected) = 1/2
T(competitor) = -1/2
J_H3 = 1/2 exactly
```

Here the final decision regret is zero, so this also shows why H3-old must be
falsified and proved as its own stronger intermediate statement rather than
inferred from final-regret experiments.

## Falsification update

The falsifier objective is now exactly

```text
J_H3 = (T(S_C) - min_{|T|=k} T(T)) / ((m-1) delta_square).
```

A fresh directed binary boundary campaign reached
`0.49999999999936096` without exceeding `1/2`; rationalization gives the
strict-Top-C equality witness above.  This is sharpness evidence, not proof.

The exchange argument currently proves the analytic cost of changing a set of
retained coordinates: changing `r` selected coordinates in one endpoint costs
at most `r * delta`.  Applying it to both extrema yields the intended H3 bound
whenever `2 * |S_C \ T| <= m-1`.  The remaining proof bottleneck is the single
balanced-complement case (`m` even, `k=m/2`, disjoint selected/competitor),
where the naive two-endpoint argument spends one extra `delta`.  No stronger
assumption has been added to hide this edge case.

### Balanced one-swap route rejected

The proposed repair “one Top-C-ordered swap costs at most `delta/2`” is false,
even in the exact balanced-complement case.  The zero-sorry module
`LeanD6BalancedExchangeCounterexample.lean` compiles an integer Fin-4/Fin-2
point-mass witness with Top-C set `{0,1}`, `deltaSquare = 17`, and four swap
decrements

```text
12, 11, 11, 21/2,
```

all strictly larger than `17/2`.  Therefore the BEX → balanced complement →
H3 proof tree is closed-rejected.  This counterexample does **not** refute H3:
the direct selected-to-complement transfer difference is `37/2`, below the H3
budget `3*17/2 = 51/2`.  The remaining valid target is consequently a direct
multi-swap/balanced argument that exploits cancellation across the complete
path, not a cheap first exchange.

## Reproduce

Use the pinned Lean 4.34.0-rc2 / Mathlib
`1f495c611d05d2215058cd77c7897d625bc3b445` environment and the fresh P12
build at `/private/tmp/cig-amf-lean-v7-runtime/high-value-build-20260830`.

Compile `LeanD6HalfFactorCore.lean` first, then
`LeanD6HalfFactorSharpness.lean`.  Do not promote the original conjecture until
H3 compiles with zero `sorry`, zero `admit`, and zero user axioms.
