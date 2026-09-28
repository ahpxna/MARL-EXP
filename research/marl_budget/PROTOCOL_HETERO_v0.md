# PROTOCOL_HETERO v0 — one broadcast stream, heterogeneous receivers, bounded patches

This is written BEFORE running the exact oracle diagnostic (`scripts/MARL_hetero_exact_oracle.py`).
It answers audit MARL_CHEAP_V2_INDEPENDENT_AUDIT §1–§3 and Step 2. It does not edit any ledger.

## 1. Model

**Receivers and capacities.**
- Every intersection i is a receiver with a decode capacity k_i ∈ {1,…,m−2}: the number of OTHER
  agents' packets it can decode at this decision step. Its own packet is never counted.
- This is the "fresh other-packet capacity" model named in the audit (§1). It is not a stream-slot
  limit.

**Timing per decision step.**
1. Public context z: paid past packets and time.
2. The scheduler PREPARES a base order π of all senders. The capacity vector K is not yet known.
3. K is revealed.
4. **Patch (radius R).** Each receiver i gets a final set S_i with |S_i| = k_i, S_i ⊆ others, and
   |S_i \ P_i| ≤ R, where P_i is the first k_i entries of π with i removed. R = 0 is the pure
   prefix.
5. **Transmission.**
   - One broadcast stream in order π, of length L0: the shortest prefix of π that contains every
     P_i.
   - Every patch-in sender outside that prefix is broadcast once more, after the stream.
   - Each receiver decodes exactly S_i.
6. Actors (frozen MP2) act on their own sensor plus the payloads in S_i. Value is the held-phase
   rollout value over H = 3 decisions, as in the v2 tables.

**Bytes.**
- Patched: 25·|T| + 3·Σ_i |S_i \ P_i|, where T = prefix(π, L0) ∪ ⋃_i S_i.
- Patch instruction: 3 bytes (receiver, drop, take).
- A packet a receiver decides not to decode was still transmitted and is still paid (§2.4 of the
  audit).
- Private unrestricted sets (comparator): T = ⋃_i S_i, plus 2 bytes per receiver for its set.
- The constant schedule header is ignored in comparisons.
- When several sets give the same actions, bytes are reported for a canonical realisation: fewest
  replacements, then fewest senders outside the prefix, then smallest mask. This is not the byte
  minimum.

## 2. Comparators, per snapshot x and revealed vector K

| name | order chosen | after reveal | status |
|---|---|---|---|
| `adv_R0`, `adv_R1`, `adv_R2` | π_adv = argmax_π mean over K ∈ K_train of f_x(π, K), exact over all 9! orders, fixed before evaluation | patch radius 0/1/2, exact optimum over patched profiles | oracle order (uses f_x, not K) |
| `heur_R0`, `heur_R1`, `heur_R2` | cached-queue public heuristic | patch radius 0/1/2, exact | deployable order |
| `known_shared` | argmax_π f_x(π, K), exact | none | budget-aware oracle, reported separately (audit §1) |
| `private` | none | argmax over all per-receiver sets, exact over the product of achievable actions | unrestricted oracle |
| `no_comm`, `full_comm` | — | — | references |

**Exactness.**
- Orders: all 9! = 362,880 are enumerated, and joint actions are de-duplicated before any rollout.
- Patched and private optima: enumeration of the Cartesian product of per-receiver achievable
  actions.
- If a product exceeds 20,000, that (x, K) is marked uncertified and excluded from the certified
  means. It is never silently approximated.

**Capacity vectors.**
- K_train: 8 vectors. K_eval: 8 vectors.
- Each k_i is i.i.d. uniform on {1,…,7}.
- RNG seed: 9000 + 100·traffic_seed + headway + t. K_train is drawn before K_eval.
- K_eval is never used to choose π_adv.

## 3. Preregistered snapshots

- Replay the 16 episodes of the v2 collection: traffic seeds 11–14, 21–22, 31–32 × headway 8 and
  16, with the same live protocol and budget seeds.
- Take the snapshot at decision t = 19 in each: the 4th snapshot of the v2 schedule, chosen by index
  before any gain is computed.
- If the per-snapshot runtime measured on the smoke allows it, add t = 31 for every episode.
  Otherwise report t = 19 only.

## 4. Decision rule (fixed now)

Per episode, average over the K_eval vectors, then over snapshots.

**The bounded-revision mechanism is SUPPORTED on this panel if both hold:**
- (a) mean(adv_R1 − adv_R0) > 0 in at least 12 of 16 episodes, and
- (b) across episodes, mean(adv_R1 − adv_R0) ≥ 0.25 · mean(private − adv_R0).

The extra bytes of R = 1 are reported next to (a) and (b).

**Otherwise the mechanism is not supported on this panel.** Actor training is not spent on it, and
the negative result is reported.

Also reported without a decision rule:
- known_shared − adv_R0: the cost of preparing before the reveal;
- heur_R1 − heur_R0: repair of a deployable order.

## 5. Limits fixed in advance

- Frozen MP2 actor, held-phase H = 3 value, 3×3 grid, 16 snapshots.
- π_adv uses the true value table of the snapshot, so it is a best-case advance order.
- The result is an oracle mechanism diagnostic. It says nothing about learnability, learned actors
  or closed-loop traffic.
