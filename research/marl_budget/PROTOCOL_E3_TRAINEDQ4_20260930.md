# The TRAINED compressed-payload actor under the byte-budget variant (DEVELOPMENT-CONFIRM protocol, 30/09/2026, written 02:4x EDT)

This is written BEFORE any run on the panel below.  The ledger entries are L-143 and L-149.

## Where this comes from (development panel 901–964, already seen)
- `set_fullq4_s s`: set actor trained with FULL delivery on sender-compressed payloads.
  - Trainer `scripts/MARL_e3_actor_train_delivery_v8.py` (s0) and v9 (s1, sampled audit), `--quant 4`.
  - Codebook `research/marl_budget/e3_payload_codebook_20260929.json`, fitted on TRAIN traffic, 3 B per packet.
- Deployed under the byte-budget variant of PROTOCOL_E3_BYTEBUDGET_20260929 (capacity 25·K_i bytes; with 3 B packets every
  receiver decodes all 8; 27 B/step), with a fresh-only receiver.
- Against the 0-byte distilled student of the same seed: s0 −4.6 % [−5.4, −3.8], s1 −4.3 % [−5.2, −3.4].
- Against set_none_s1: −10.3 %.

## Hypothesis
Training the actor on compressed decision summaries (not only compressing afterwards) beats the best 0-byte policy under the
byte-budget variant, at 27 B/step.

## Arms, seeds, comparators
- Arm: set_fullq4_s s, s ∈ {0, 1}.  Evaluator `scripts/MARL_e3_delivery_eval_v7.py --quant 4 --byte-capacity 3
  --adapter-override freshonly --deliveries prefix` (full per-step audit).
- PRIMARY comparator: distill_none_s s (0 B), evaluated with v6 and no messages.
- Secondary:
  - set_none_s s;
  - the eval-only-compressed raw teacher set_full_s s under the same variant;
  - maxq.

## Panel
- **Traffic seeds 2401–2464 × headways 8 / 16** (128 episodes), checked unused for any E3 episode at 02:4x.
- It is used once.

## Pre-stated criterion
- **PRIMARY**, per seed s:
  - statistic: the ratio of summed waiting, arm / distill_none_s s, minus 1;
  - bootstrap over traffic seeds, both headways, 4000 resamples;
  - the upper 95 % bound must be < 0.
- It is supported only if BOTH seeds pass.

## Not claimed
- This is not the reserved test (1301–1316 stays closed).
- The byte-budget capacity model is a declared alternative to HETERO_v0's packet model.
