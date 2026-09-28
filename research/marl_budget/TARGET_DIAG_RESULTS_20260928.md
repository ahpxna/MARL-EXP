# Target diagnostic: held-phase labels against closed-loop continuation labels (28/09/2026, 00:12)

- **Evidence class.** Oracle-label diagnostic on development states (opened). Not a learner, not a
  test. No ledger is edited.
- **Asked by.** The independent readiness audit §4.6 ("held-phase target mismatch remains another
  hypothesis"), and made necessary by B4: the retrained selectors edit as often as the oracle but
  do not gain (`B4_DAGGER_RESULTS_20260928.md`).

## Design

**Producer.** `scripts/MARL_hetero_target_diag.py`. Run `target_diag_20260928_000455/`; the
manifest has the source hashes. Smoke run `target_diag_smoke_20260928_000439b/`.

**States.** Development seeds 501–504 × headways 8, 16, at snapshots t ∈ {10, 16} on the prefix
trajectory: 16 states, 8 episodes.
- Live K.
- The B1 candidate family: 160–196 candidates per state, all within +84 B.

**Two labels for every candidate S, same state, same seeded capacity trace, same H = 3.**
- **held_3(S):** the training label. The joint action of S is held for 3 decisions, and the value
  is −Σ waiting at the 3 boundaries (`oracle_rollout_value`).
- **cont_3(S):** S is transmitted at step t. Steps t+1 and t+2 then run the live loop with the
  DECLARED continuation: prefix scheduler, frozen MP2 acting on the received views, caches updated
  by what S delivered. The value is −Σ waiting at the same 3 boundaries.
- The continuation is computed by re-running the deterministic episode from reset to t with the
  prefix policy, on a fresh engine per candidate.

**Self-checks (each can fail): PASS, 0 failures.**
1. Every replay reproduces the base run's order and K at t.
2. cont_1(S) = held_1(S) exactly, and the live joint action equals the counterfactual-view joint
   action, for all 2,810 candidates. The one-step value and the action wiring agree.
3. cont_3(P) equals the base run's −(q_t + q_{t+1} + q_{t+2}) for the prefix P.

## Result

Gains are relative to the prefix at the same state. The bootstrap is over the 8 episodes
(per-episode means).

| quantity | value |
|---|---|
| held-phase argmax equals the continuation argmax (value ties count as agreement) | **1 of 16 states (6%)**; 2/16 among action-changing candidates |
| held-phase best gain (in its own label) | +18.6 [+9.9, +28.3] |
| **continuation gain realised by the held-phase argmax** | **+9.5 [+2.8, +18.3]** |
| continuation best gain | +19.4 [+13.8, +25.9] |
| continuation regret of the held-phase argmax | +9.9 [+5.4, +14.8] |
| share of the continuation headroom captured by the held-phase argmax | 49% |
| states where the held-phase argmax is WORSE than the prefix in continuation | 4 of 16 |
| mean Spearman correlation of the two gain vectors | 0.41 (range −0.48 to 0.93) |
| among candidates with a positive held-phase gain, share with a positive continuation gain | 62% |

## Reading

1. **The target mismatch is real and material.**
   - Even a PERFECT held-phase oracle chooses the continuation-best profile in only 1 of 16
     states.
   - It captures about half of the one-step continuation headroom.
   - It makes things worse than the prefix in a quarter of the states.
   - The mismatch has two sources:
     - holding the phase fixed (the live loop re-acts);
     - ignoring what S leaves in the receivers' caches for later steps.
2. **It does not explain the whole closed-loop shortfall.**
   - The held-phase oracle, applied every step, still gives −15.0% Σ waiting in closed loop (B4).
   - The learned selectors realise only about 4.5% of that, and about 18% of the held-phase oracle
     gain even in the held phase (B2).
   - So estimation error remains the larger factor. The target mismatch caps what a perfect
     held-phase learner could reach.
3. **Scope.**
   - The continuation is short (H = 3) and uses the prefix scheduler as the declared continuation;
     it is not the full-episode return of the deployed policy.
   - 16 development states; frozen MP2; 3×3 grid.

## Consequence for E3 (actor pilot)

- The evaluator target must be declared, as in the readiness audit §5:
  f_X^{π,c}(S) = E[return | X, first profile S, continuation c].
- The held-phase label should either be replaced by, or reported alongside, a continuation label
  for the new actor.
- The producer here is reusable: it only needs the actor and continuation callables.
- The fixed-MP2 selector results (B2, B4) stay as they are, labelled "held-phase target".
