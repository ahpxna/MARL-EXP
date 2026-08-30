# Structural Final Kill Gate

Exact characterization search remains closed. No adjacent, submodular, supermodular, M-convex, monotonicity, deficit, or extrema-compatibility iff was reopened.

## Corpus

The focused approximate/algorithmic round evaluated 106,130 exact-integer support-radius worlds:

- existing exhaustive `m=3`: 12,352;
- existing exhaustive `m=4` support slice: 63,775;
- existing random `m=4/5/6`: 15,000;
- fresh sparse/cancellation-biased adversarial `m=4/5/6`: 15,000;
- frozen W1/W2/W3: 3.

## Direction 1 — approximate rankability

- Weak adjacent nesting defect: `KILLED` by 711 zero-defect positive-regret worlds.
- All-optimal extension defect: `OPEN`. The candidate
  `best all-budget chain regret <= m * defect`
  survived all 106,130 support-radius worlds. It failed on arbitrary set functions, so a valid proof would need a genuinely support-specific argument. No theorem is claimed.
- A path-bottleneck defect equal by construction to best nested-chain regret was rejected as a renamed target, not formalized.

## Direction 2 — complexity / algorithmic

Lean proves the exact search-space facts:

- subset-lattice dynamic-programming states: `2^m`;
- full rankings: `m!`.

The tested local one-swap trap depth did not reliably predict existence of a low-regret nested chain: 3,733 false positives and 2,629 false negatives. This predictor is `KILLED`. Claims about empirical runtime prediction remain experiment-only.

## Direction 3 — negative structural taxonomy

`STAX_actual_support_radius_three_way_taxonomy` is `PROVED` and combines W1/W2/W3 inside the actual CIG-AMF `selectedRadius` class.

## Gate decision

`STOP STRUCTURAL EXACT THEORY SEARCH` remains active. The only surviving new approximate statement is explicitly `OPEN`; it does not authorize another broad characterization round.

Raw evidence: `compile_logs/structural_approximate_final_results.json`.
