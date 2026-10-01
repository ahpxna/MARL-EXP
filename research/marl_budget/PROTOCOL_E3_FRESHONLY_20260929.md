# Replicating "full-information training, fresh-only deployment" (DEVELOPMENT-CONFIRM protocol, 29/09/2026, written 22:2x EDT)

This is written BEFORE any run it describes: the seed-1 teacher is not yet trained, and no episode of panel 2001–2064 has
been simulated.  The ledger entries are L-123 … L-125 in `research/papers/audits/MARL_SELF_AUDIT_LEDGER_20260928.md`.

## Where this comes from (development, panel 901–964, already used many times today)
- The set-structured actor trained with FULL fresh delivery (`set_full_s0`, 225 B/step) is −5.8 % [−6.7, −5.0] vs the
  same-architecture co-trained none actor under full delivery.  With the protocol's prefix it drops to −0.1 %; with caps
  4 and 6 it is +1.7 … +1.8 %.  This is the capacity cliff (L-123).
- D3 (L-124, reading rule written before the result): at deployment, pool only the packets decoded THIS step (stale
  cached blocks dropped, `FreshOnlyCommAdapter` sets them to not-heard).
  - This gives −3.3 % [−4.2, −2.4] under the prefix (188.7 B/step).
  - It gives −3.5 % [−4.3, −2.6] under cap 4 (100 B/step), vs set_none_s0.
  - Under capacities 5–7 it gives −6.0 %, equal to full delivery.
- Selection on this panel: two receiver rules were compared (stale kept, stale dropped) on one actor seed.  That panel
  therefore cannot confirm the rule.

## The method under test (FO)
- **Training:** the set actor (`models/marl_comm_actor_set.py`, SetActorNet) under FULL delivery.
  - Trainer `scripts/MARL_e3_actor_train_delivery_v6.py --set-actor --delivery full`, the scratch recipe: 2000 iterations,
    8 episodes/iteration, 4 epochs, minibatch 64, lr 3e-4, entropy 0.01, hidden 128, eval every 20, 2 threads.
  - Checkpoint `ckpt_best.pt` on SELECT (401–408).
  - Full delivery in training is a declared requirement: it needs full-bandwidth messages in the simulator, as a
    centralised critic needs global state.
- **Deployment:** the protocol's broadcast prefix stream with capacities K_i ~ U{1..7} i.i.d. per step
  (PROTOCOL_HETERO_v0).  Stream bytes are accounted exactly as for the prefix system.
  - Each receiver uses only the packets it decoded this step.  Cached (stale) blocks are masked as not heard.
  - The rule reads only the receiver's own view (its fresh flags), so it is legal at deployment.
  - Evaluation: `scripts/MARL_e3_delivery_eval_v6.py --adapter-override freshonly`.

## Arms and seeds
- Training seeds 0 (`set_full_s0`, exists) and 1 (`set_full_s1`, to train).
- References of the same architecture and training seed: `set_none_s0` (exists) and `set_none_s1` (training now, 22:2x).
- Also reported, each actor on each panel:
  - FO under cap 4 (secondary, 100 B/step);
  - the same actors with stale blocks KEPT (default adapter) under the prefix;
  - full delivery (the ceiling, 225 B/step);
  - the co-trained prefix set actors `set_prefix_s0/_s1`;
  - maxq (0 B).

## Panels
- **NEW panel: traffic seeds 2001–2064 × headways 8 and 16** (128 episodes).
  - Used once, for this comparison only.
  - It was checked unused for any E3 episode at 22:2x.  The used ranges are 301–364 (TRAIN), 401–408 (SELECT),
    501–504, 601–616, 801–816, 901–964, 1001–1068, 1101–1116; 1301–1316 is the reserved test and stays closed.
- Also: the development panel 901–964 for seed 1 (development only).

## Pre-stated criterion
- **PRIMARY**, per training seed s ∈ {0, 1}, on panel 2001–2064:
  - statistic: the ratio of summed waiting FO(set_full_s s) under the prefix / set_none_s s with no messages, minus 1;
  - bootstrap over traffic seeds, both headways together, 4000 resamples, 95 % percentile interval;
  - the upper bound must be < 0.
- **FO is supported** only if BOTH seeds pass.
- **If exactly one seed passes**, the result is reported as seed-dependent.
- **If neither passes**, D3 was panel-specific and FO is reported as a negative.
- **Secondary**, reported as measured with no pass/fail: cap 4; vs set_prefix; vs maxq; by headway; the stale-kept
  adapter; full.

## Not claimed, whatever the outcome
- This is not the reserved test.
- It does not show that full-information training is necessary: a set actor trained under the prefix with fresh-only
  inputs is a different arm, not run here.
- It does not transfer any theorem.
