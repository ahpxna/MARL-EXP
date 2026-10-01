# A fresh-only set receiver TRAINED under the protocol's own prefix (DEVELOPMENT-CONFIRM protocol, 29/09/2026, written 23:4x EDT)

This is written BEFORE any run on the panel below.  The ledger entry is L-139.

## Where this comes from (development panel 901–964, already seen)
- `set_fresh_s0`: the set actor (SetActorNet), trained with the scratch MAPPO recipe under the PREFIX delivery of
  PROTOCOL_HETERO_v0 (K_i ~ U{1..7}, 25 B payloads).  It has FRESH-ONLY inputs: cached stale blocks are masked as not heard
  (FreshOnlyCommAdapter), in training and at deployment.  No teacher, no full-bandwidth training.
- Trainer `scripts/MARL_e3_actor_train_delivery_v7.py --arch set --adapter freshonly --delivery prefix`; best select 1155.3.
- Under the prefix (188.7 B/step):
  - −5.8 % vs set_none_s0;
  - **−2.7 % [−3.6, −1.8] vs the 0-byte distilled student distill_none_s0**;
  - −2.7 % vs FO;
  - −3.9 % vs set_prefix_s0 (the same actor trained with stale blocks kept).
- Cap 4 (100 B/step): −2.6 % vs the student.
- It CONTRADICTED my prediction from its SELECT curve at 80 % of training (ledger L-139).  One seed.

## Hypothesis
Inside HETERO_v0, unchanged, a set receiver that uses only this step's decoded packets beats the best 0-byte policy
(the distilled student) and the same-architecture no-communication actor.  It needs no teacher and no full-bandwidth
training.

## Arms and seeds
- `set_fresh_s s`, s ∈ {0, 1}.  s = 1 is training since 23:4x with trainer v9 (identical recipe, sampled audit).
- Comparators:
  - PRIMARY: the 0-byte student distill_none_s s;
  - SECONDARY: set_none_s s, set_prefix_s s, maxq;
  - the student with fresh-only messages distill_fo_prefix_s s, reported as measured.

## Panel
- **Traffic seeds 2301–2364 × headways 8 / 16** (128 episodes), checked unused for any E3 episode at 23:4x.
- It is used once.

## Pre-stated criterion
- **PRIMARY**, per seed s:
  - statistic: set_fresh_s s under the prefix vs distill_none_s s with no messages;
  - bootstrap over traffic seeds, both headways, 4000 resamples;
  - the upper 95 % bound must be < 0.
- It is supported only if BOTH seeds pass.
- Also reported against set_none_s s with the same statistic, and under cap 4.
- Evaluator: `scripts/MARL_e3_delivery_eval_v6.py` (adapter from the checkpoint; full per-step access audit).

## Not claimed
- This is not the reserved test (1301–1316 stays closed).
- One recipe, not tuned.
