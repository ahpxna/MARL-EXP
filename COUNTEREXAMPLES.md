# Counterexamples and Exact Witnesses

## Reference non-identifiability

`LeanReferenceIdentifiabilityV1.lean` gives two valid `Fin 2 -> Fin 2` conditional kernels. They agree on the sole observed source action `0` and disagree at unobserved action `1`. With the binary complement signal:

- flat kernel: `chi = 0`;
- reactive kernel: `chi = 1`.

Adding a second relation of fixed span `1/2` makes the unique Top-1 decision change from relation 1 to relation 0. This is a downstream non-identifiability witness, not merely unequal hidden tables.

## Weak adjacent structural defect is insufficient

Minimal stored support-radius witness from the exhaustive `m=4` slice:

```text
support = {(0,1,1,0), (1,0,0,1)}
slopes  = (-3,-1,2,4)
weak adjacent defect = 0
best nested-chain regret (twice radius) = 1
```

Across 106,130 worlds, 711 worlds had zero weak-adjacent defect but positive best-chain regret.

## Local one-swap traps do not characterize rankability

The local-trap predictor produced 3,733 false positives and 2,629 false negatives relative to positive best all-budget nested-chain regret. It is therefore killed as either a sufficient or necessary characterization.

## Arbitrary set functions reject the surviving support-specific candidate

The empirical candidate `best-chain regret <= m * all-optimal-extension defect` survived all 106,130 `selectedRadius` worlds, but it is false for arbitrary set functions. One exact `m=4` arbitrary objective has target regret 8 and defect 1, violating `8 <= 4`. Therefore any proof must use support-radius structure; the package records the specialized candidate as `OPEN`.

## Covariance design reversal

`FCOV_design_misranking_witness` uses two PSD matrices:

```text
SigmaA = [[1, 9/10], [9/10, 1]]
SigmaB = [[3/5, -1/2], [-1/2, 3/5]]
vC     = (1,-1)
```

Diagonal-only variance ranks B below A, while full quadratic variance ranks A below B.

## Frozen actual structural taxonomy

The final taxonomy reuses actual `selectedRadius` witnesses:

- W1: scalar-prefix rankable but Top-C not exact;
- W2: Top-C exact at all budgets but not globally co-extremizable;
- W3: unique nonnested budget optima, hence not scalar-prefix rankable.
