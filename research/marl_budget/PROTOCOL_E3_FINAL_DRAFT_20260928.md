# E3 FINAL PROTOCOL — DRAFT, NOT FROZEN (28/09/2026, 14:13; handoff F6, independent recheck P3)

This is a working draft.
- It freezes nothing, and seeds 1301–1316 stay closed.
- It becomes the final protocol only when every OPEN item below is decided, every checkpoint hash is filled
  in, and a dated FROZEN copy with its own sha256 is written. After that, no code or method may change before
  the single test run.
- Any change made after seeing test results turns the panel into development data for a new version.

## 1. Actors (all seeds reported: PROTOCOL_DEVIATION_E3_SEEDS_20260928.md)
- Scratch recipe (per-seed gate): seeds 0–4. Warm-started recipe (gate on pilot s0, which FAILED; recorded,
  never confirmatory): seeds 0–4. Mixed-profile pilot: s3.
- The checkpoint is `ckpt_best.pt` of each actor, with its sha256 recorded here at freeze.
- OPEN: which gated actors enter the test. Rule proposed: EVERY scratch seed that passes G1/G2 on development,
  with the pass rate reported, plus every other finished actor reported descriptively.

## 2. Methods (every one on the SAME frozen actor checkpoint)
Runtime `scripts/MARL_e3_closed_loop_v5.py`, with its self-checks: τ parsing, score/choice parity with the
trainer, per-step byte parity.

| method | role |
|---|---|
| committed prefix (R = 0) | reference |
| direct no-bid selector | comparator (price of commitment) |
| direct response-bid selector (the method) | proposed |
| R1 policy | ablation, not required to beat direct |
| learned SchedNet-style frozen-actor adaptation (1 B weights) | comparator (an adaptation, not the original) |
| same-byte queue bid (10 B) | alternative-information control |
| oracle over the same candidates | diagnostic, not deployable |

OPEN: which selector recipe is "the method". Rule: chosen on SELECT by DECISION quality (realised gain, harm |
edit, regret), never by MSE or head accuracy, and never on development or test data. The τ grid includes +∞.
If the chosen τ is +∞, the method never edits: that shows harm avoidance, not a benefit.

## 3. Resources
- Total cap = the prefix's own bytes + a fixed allowance. The allowance points are +28, +56, +84 and +140 if a
  frontier is claimed; they are fixed here and never chosen on the test.
- Bids are charged 10 B at every step inside the cap.
- Absolute charged bytes per step are reported for every method. Compute is reported, and no latency advantage
  is claimed.

## 4. Primary endpoint — OPEN (the authors' decision, before the test)
- The primary endpoint is episode Σ waiting of the method against the SAME actor's prefix, paired by episode.
- OPEN: the endpoint TYPE is one of:
  - (a) superiority at one fixed cap;
  - (b) non-inferiority within a PRE-SET margin at fewer bytes;
  - (c) stability across budgets at equal cost.
- A CI containing 0 is never read as equivalence.
- Guardrails: finished trips, throughput, censored travel time and unfinished trips.

## 5. Panel and aggregation
- Traffic seeds 1301–1316 × headways 8 and 16 (32 episodes). One declared shift is proposed: bursty
  capacities.
- Uncertainty uses a two-level bootstrap: actor seeds, then traffic seeds, with both loads of a seed kept
  together. Selector init seeds are averaged within an actor; they are not replications.
- Every endpoint, failure, retry, censoring and oracle-access check is reported.

## 6. What must be true before freezing
- Development results are complete: F1 dense, F2-C mix, all scratch seeds.
- Only recipes with a development signal enter closed loop. If none has a signal, the protocol still tests
  the frozen best-on-SELECT recipe, OR the authors change scope. That is their decision, not the worker's.
