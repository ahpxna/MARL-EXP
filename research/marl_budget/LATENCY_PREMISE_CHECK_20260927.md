# Latency-premise check of PROTOCOL_v1, plus the cheap screen and pilot — 27/09/2026

This file does not edit any ledger. Nothing here is gated, and nothing may enter a manuscript from it
until the gate runs.

## 1. The argument (zero compute)

Under PROTOCOL_v1, a budget-conditioned baseline sees the grant k at the same moment as the method
and gets the same precompute allowance. The grant set is finite, k ∈ {1,…,m−1}. The baseline can
therefore build a table k ↦ Ŝ(k) BEFORE the grant and answer by lookup afterwards. Two facts follow:

- **Quality:** the table is at least as good as prefix-plus-revision, because every revision output is
  a k-set.
- **Latency:** after the grant, the table costs one lookup, no more than cutting a prefix.

Formal value side, compiled with standard axioms and 0 sorry, not gated:
`work/p13_conjectures/LeanMarlTabulationV1.lean`.
- `reach_card`
- `tabulated_regret`: regret ≤ 2ε + ν, with no geometric term.
- `tabulation_dominates_revision`
- `exact_tabulation_dominates`
- `tabulation_regret_sharp`: the 2ε is attained.

## 2. Measured latency

Setup:
- Networks from pilot `cheap_pilot_20260927_165828`, checkpoint seed 0.
- m = 9, CPU, one torch thread.
- Median of repeated calls, one context.
- Script: `research/marl_budget/latency_check_20260927/latency_bench.py`. Result: `latency_result.json` in the same folder.

| phase | operation | µs |
|---|---|---|
| before grant | priority (score forward + argsort) | 23.7 |
| before grant | direct budget table (one forward, all k) | 64.5 |
| before grant | critic table (one forward over all 512 sets, per-k argmax) | 209.9 |
| after grant | cut prefix | 0.3–0.5 |
| after grant | table lookup | 0.0–0.1 |
| after grant | R=1 repair, critic precomputed | 6.8–19.1 |
| after grant | R=1 repair, fresh critic call | 35.6–44.5 |
| after grant | R=2 repair, fresh critic call | 35.4–58.6 |
| after grant | unrestricted search, fresh critic call | 35.4–69.2 |

Reading:
- After the grant, tabulation is at least as fast as the prefix. Revision is 10²–10³ times slower than a
  lookup.
- The priority's only saving is before the grant, and it is about 40 µs against the direct table.
- Every number is 5–6 orders of magnitude below the 10 s decision interval.

**Verdict:** in PROTOCOL_v1 the claim "a prepared priority has a runtime advantage" does not hold. The
scope's own stopping rule (MARL_FINAL_SCOPE §1, §7) says to drop it, not to change the benchmark.

## 3. Headroom screen (oracle f_joint)

Setup:
- Frozen MP2 actor, H = 3 held-phase decisions, 3×3 grid, global broadcast.
- Datasets:
  - `cheap_screen_20260927_165721`: 24 tables, sha f9a2a3a9…;
  - `cheap_pilot_20260927_165828/data`: 192 tables, sha d48504ee…
- Re-analysed from the raw tables by `research/marl_budget/latency_check_20260927/analyse_screen.py`. Means are taken per episode,
  then across episodes.

| quantity (192 tables, 16 episodes) | regret | fraction of spread |
|---|---|---|
| spread of k-set values | 49.6 (\|best\| ≈ 520) | 1 |
| cached-queue prefix (public heuristic) | 23.1 | 0.46 |
| its oracle R=1 / R=2 repair | 4.09 / 0.54 | 0.07 / 0.01 |
| true-singleton-gain prefix (oracle score) | 8.05 | 0.16 |
| its oracle R=1 repair | 1.15 | 0.02 |
| best nested chain (oracle, minimum over the sum across k) | 0.33 | < 0.01 |

On this panel the loss comes from the score, not from nesting. A good nested order is almost optimal
at every budget. The 24-table screen gives the same pattern.

## 4. Pilot: can permitted information realise the headroom?

Setup:
- 96 train, 48 val and 48 test contexts, with episodes kept separate across splits.
- Three initialisation seeds, 150 epochs, about 12k parameters per network.
- Numbers are mean episode regret, as mean over seeds and the range across seeds. The critic-chain rows and the train column come from `latency_check_20260927/extra_baselines.py`; raw output is `extra_baselines_and_latency_output.txt`.

| method | test | train |
|---|---|---|
| cached-queue prefix | 24.5 | — |
| learned score prefix | 22.8 (21.2–25.6) | 16.6 |
| learned repair R=1 | 24.3 (22.9–26.3) | 19.2 |
| learned repair R=2 | 24.0 (23.3–24.4) | — |
| priority derived from the critic (one chain for all k) | 24.5 | 22.2 |
| same chain + R=1 repair | 24.3 | 22.1 |
| critic unrestricted (= per-budget table) | 24.3 | 22.1 |
| direct budget network | 23.4 (22.4–24.1) | 6.7 |
| oracle R=1 repair of learned score | 3.4–4.9 | — |
| oracle per-budget | 0 | 0 |

Reading:
- No learned method beats the public heuristic on held-out episodes by more than about 7%.
- Learned repair is WORSE than its own prefix on both train and test. With an evaluator error this
  large, repair hurts, which is exactly the 2ε term of T1.
- The direct network fits train (6.7) and fails on test (23.4). This is a generalisation gap whose
  cause is unresolved (corrected 27/09, see MARL_CHEAP_V2_INDEPENDENT_AUDIT §5).
- The critic fails even on train. MSE over all 512 values does not rank within a layer.
- Critic chain, critic unrestricted and critic chain + R1 have similar MEAN regret. This does not
  show identical selections or zero nesting cost (corrected; see audit §7).
- The v3 decision records measure this directly. The critic's prepared chain and its per-budget
  table choose different sets in 2–15% of decisions, with paired per-episode differences within
  about ±4.

## 5. What this does to the direction

1. **Drop the latency/precommitment advantage under PROTOCOL_v1** (§2). A prepared priority can still
   matter only if one of the following holds:
   - **Nesting is physically forced:** one broadcast stream read by receivers with different budgets,
     or a channel cut at an unknown time. There a per-budget table is infeasible, and T1/T2 apply.
   - **Generalisation or sample efficiency:** one ranking plus a repair learns from less data, or
     generalises to unseen grants, better than a K-headed selector. This is untested; §4 says neither
     learns yet.
2. **The traffic evidence does not support "all rankings fail".** It supports "the deployable score is
   wrong", and a better ranking is nearly optimal (§3). Correcting the score is the whole problem.
3. **Oracle headroom is large, learned headroom is about zero** (§4). Why is not identified.
   Candidates are the information rule (the inputs are only stale, already-paid packets), data,
   model or distribution shift. Adding privileged current summaries did not close it (v2/v3), and
   that does not rule the information rule in or out. (Corrected 27/09.)

## 6. Next cheap checks (each is minutes)

- **Information ceiling.** Same pilot, but give the selectors the true current per-intersection
  waiting counts.
  - If test regret falls toward the oracle, the bottleneck is the public-scheduler information rule.
  - If it does not fall, the bottleneck is data or model.
- **Fresh-bid protocol.** Each agent sends a 1-byte fresh importance bid, charged as control bytes,
  as in SchedNet's weight-based scheduling. Selectors see the bids. This is the fair version of
  PROTOCOL_v1's "charged metadata" clause and the natural baseline.
- **Unseen-budget generalisation.** Train on k ∈ {2,4,6} and test on {3,5,7}. This is the only place
  a single priority could beat a K-headed direct network under PROTOCOL_v1.
- **Heterogeneous-receiver broadcast.** Receivers with different budgets read one stream. Measure the
  headroom of per-receiver sets over one shared order. This decides whether the nested setting has
  traffic value.

## 7. Provenance

Every producer file under test is untracked in git:
- `scripts/MARL_cheap_screen.py`
- `scripts/MARL_cheap_pilot.py`
- `models/marl_screening.py`
- `envs/external/cityflow_broadcast.py`

The manifests record SHA-256 of the sources:
- screen source 2b2388f5… (screen script) at collection time;
- the pilot report's `data_table_sha256` matches the data manifest.

Unit tests: 13/13 PASS, re-run in this session. Collection assertions (`no_oracle_access` around live
selection, packet accounting) were active and did not fire.
