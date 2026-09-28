# Exact oracle mechanism test under PROTOCOL_HETERO_v0 — results, 27/09/2026

This file does not edit any ledger and has not been gated. It is an oracle mechanism diagnostic, not
learned MARL.

## Provenance

- **Protocol and preregistration:** `research/marl_budget/PROTOCOL_HETERO_v0.md`, written before the
  run. Its sha is recorded in the manifest.
- **Producer:** `scripts/MARL_hetero_exact_oracle.py`.
  - It replays the 16 v2 episodes: traffic seeds 11–14, 21–22, 31–32 × headway 8/16.
  - Snapshots t = 19 and t = 31, preregistered: 32 snapshots in total.
  - 8 K_train and 8 K_eval capacity vectors per snapshot, k_i uniform on {1,…,7}.
- **Data:** `research/marl_budget/hetero_exact_20260927_173902/records.jsonl.gz`. manifest COMPLETE,
  32 records, sha 66241623…, 186 s.
- **Exactness:**
  - all 9! base orders enumerated;
  - patched and private optima by full enumeration of achievable-action products;
  - 0 of 256 (snapshot, K) pairs above the cap, so every number below is certified exact for the
    stated model.
- **Legality asserts in the producer:** |S_i| = k_i, own packet excluded, |S_i \ P_i| ≤ R. None
  fired.
- **Analysis:** `research/marl_budget/latency_check_20260927/analyse_hetero_exact.py`. Averages are
  per episode, then across 16 episodes.

## Results

Values are held-phase values over H = 3 (minus summed waiting counts at the 3 decision boundaries;
higher is better). They are not delay or unique vehicles.

| comparison | mean gain | episode range | episodes > 0 |
|---|---|---|---|
| adv_R1 − adv_R0 (one patch per receiver, order prepared before the reveal) | **+8.45** | +2.25 … +23.38 | **16/16** |
| adv_R2 − adv_R0 | +9.62 | +2.25 … +30.75 | 16/16 |
| private − adv_R0 (unrestricted per-receiver sets) | +9.62 | +2.25 … +30.75 | 16/16 |
| known_shared − adv_R0 (cost of preparing before the reveal) | +6.86 | +1.81 … +20.44 | 16/16 |
| adv_R0 − heur_R0 (oracle advance order vs public heuristic) | +21.05 | +4.50 … +44.31 | 16/16 |
| heur_R1 − heur_R0 (one patch on the deployable heuristic order) | +27.22 | +11.06 … +48.38 | 16/16 |
| heur_R2 − heur_R0 | +30.22 | +11.06 … +58.62 | 16/16 |
| private − heur_R0 | +30.67 | +11.06 … +58.62 | 16/16 |

Extra bytes over the pure prefix (25 B per packet, 3 B per patch instruction):

| comparison | mean extra bytes | episode range |
|---|---|---|
| adv_R1 | +15.7 | +0.8 … +32.1 |
| heur_R1 | +26.5 | +14.8 … +36.4 |
| private over adv_R0 | +33.7 | +21.1 … +49.3 |

Receiver capacities are fixed, so these bytes buy a different choice of packets, not more of them.

**Preregistered decision rule (§4):**
- (a) 16/16 episodes positive (needed ≥ 12): passes.
- (b) R = 1 recovers 0.88 of the private gap (needed ≥ 0.25): passes.
- **The mechanism is SUPPORTED on this panel.**

## Reading

- On one broadcast stream with heterogeneous receivers, a single patch per receiver after the reveal
  recovers 88% of what unrestricted per-receiver sets achieve. Two patches recover all of it in this
  panel.
- The 88% is measured from an advance order that is already oracle-optimal for the capacity
  distribution. On the deployable public heuristic order, one patch recovers 89% (27.2 of 30.7).
- The prepared order plus one patch (+8.45) beats even the budget-aware best shared order
  (+6.86 over adv_R0). The patch removes the cost of committing the order before the reveal.
- Patching costs about 16–26 extra bytes per step, against a stream of about 175–225 bytes.

## What this does NOT show

- **Learnability.** Every comparator uses the true value of the snapshot. π_adv uses those values
  too, so it is a best-case advance order.
- **Learned actors or closed-loop traffic.** The actor is frozen MP2, the value is held-phase with
  H = 3, and there is no continuation.
- **Generality.** The panel is 32 snapshots, 8 traffic seed IDs × 2 loads, one 3×3 grid, and one
  capacity distribution. MP2 has few distinct actions per receiver, which is why R = 2 already
  reaches the private optimum.
- **Byte optimality.** Bytes are those of a canonical realisation, not the byte minimum.

## Next step (audit Step 3, only now justified)

Run a learning curve on THIS objective:
- a learned shared order, plus learned bounded repair, plus a direct budget-aware comparator;
- the same legal information and the same total bytes for every method;
- new independent traffic seeds, nested training sizes 96/192/384/768, and a fresh untouched test
  panel;
- raw decisions, checkpoints and source hashes saved.

Actor training and closed-loop evaluation come after that.
