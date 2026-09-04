# D6 contrast-rank mechanism — status (2026-09-03)

All modules listed below compile against the pinned Lean toolchain.  They are
P13/quarantine work and do not modify the immutable P12 baseline.

| Object | Status | Exact content | Interpretation |
|---|---|---|---|
| Centered interaction profile | PROVED | anchor zero; coordinate-additive invariance under global product normalization; exact mixed-difference identity; two-context delta bound | A mixed difference is exactly context variation of a first-order-centered local action contrast. |
| Rank-one predicate | PROVED | `Fin 2` always has rank one; rank-one profiles factor every cycle; nonzero profile determinant obstructs rank one | This captures binary geometry without using raw alphabet dimension. |
| Ternary normalized balanced witness | PROVED | coordinate 0 has determinant `-1` at exact rational contexts | The existing ternary falsifier is formally `RankNonOne`; no numerical-rank claim is encoded. |
| Strict-margin ternary witness | PROVED | spans `(21/20, 1, 21/20, 1)`; selected loss `5/2`; competitor loss `11/20`; doubled gap `39/10 > 3` | The old normalized balanced `m-1` claim fails even with strict Top-C separation; ties are not the explanation. |
| Phase language | DEFINITIONS ONLY | rank-one normalized balanced class and explicitly named phase conjectures | No theorem claims `rank one -> m-1`; that is now a falsifiable research target. |
| Safe profile quotient | PROVED | equal profiles give a context-independent local contrast after response subtraction; two-profile representative lemma | Equal profiles do not imply globally interchangeable actions. |

## Explicitly still conjectural

- all rank-one normalized balanced cells have decision constant at most `m - 1`;
- binary sharp `m - 1` for every even dimension;
- RankNonOne saturation at `m` for every even dimension;
- any equality between a decision-interaction constant and a separate
  certificate/atomic norm.

The universal normalized balanced `m - 1` theorem over arbitrary finite
action alphabets is **falsified**, not open.
