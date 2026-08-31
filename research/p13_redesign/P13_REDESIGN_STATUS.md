# P13 Lean redesign handoff

## Immutable baseline

- Lean: `4.34.0-rc2` (`6a10ac8c22beadecabdbb0919c2b50214762f91d`)
- Mathlib: `1f495c611d05d2215058cd77c7897d625bc3b445`
- Repository source: `36f652cddaf43cd7fb14a48eda00b0bd658461c8`
- The P12 sources and compiled objects are copied unchanged into the handoff.
- `LeanUnifiedChainsV2.lean` is historical and is not an active build target.

## Result classification

| Programme | Result | Status | Evidence |
|---|---|---|---|
| D6 half-factor | `decisionRegret <= (m-1) * deltaSquare / 2` | `OPEN` | Exact rational m=3 enumeration and directed m=3/m=4 searches found no counterexample. This is not a proof. |
| D6 exact search | radius-1, binary m=3, k=1/2 | `NO_COUNTEREXAMPLE_IN_SEARCH_DOMAIN` | 2,187 exact rational worlds; best `J=1/16`. |
| D6 directed search | q-skewed and q-optimized m=3/m=4 | `NO_COUNTEREXAMPLE_IN_SEARCH_DOMAIN` | Best `J=0.4687499984`, below the falsification threshold `1/2`. |
| Unknown variance | plug-in relative robustness | `LEAN_VERIFIED` if the accompanying compile exit is zero | Deterministic sandwich with factor `((1+rho)/(1-rho))^2`; no probability claim. |
| Unknown variance D | `c_i = |w_i|` specialization | `LEAN_VERIFIED` if compile exit is zero | True sigma remains oracle-only; learned sigma obeys an assumed relative-error envelope. |
| Unknown variance stable-extrema C | unit-contrast specialization | `LEAN_VERIFIED` if compile exit is zero | Applies only after extrema indices are fixed/stable. |
| Response/reference split | 2/3-power continuous allocation | `OPEN` | Quarantined source still contains `sorry`; excluded from verified targets. |
| Structural | scaled all-optimal-extension defect | `OPEN` | Exact selected-radius definitions have not yet replaced the theorem shell; excluded from verified targets. |

## D6 falsification conclusion

The directed objective is

`J = decision_regret / ((m - 1) * delta_square)`.

The conjecture is killed iff `J > 1/2`. The strongest search witness obtained
`J = 0.4687499984138005`, with `m=3`, `k=1`, `delta_square=8`, and regret
approximately `7.5`. Therefore this search does **not** kill the half-factor
candidate, but it also does not verify it.

## Scientific interpretation

- Known true `sigma` is an oracle ceiling, not a deployable allocation method.
- The new variance theorem only quantifies degradation when learned standard
  deviations satisfy a deterministic relative-error envelope.
- Probability of that envelope is a separate statistical problem.
- No quarantined theorem containing `sorry` is included in the verified ledger.

