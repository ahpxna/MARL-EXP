# A distilled student WITH fresh-only messages, inside PROTOCOL_HETERO_v0 (DEVELOPMENT-CONFIRM protocol, 29/09/2026, written 23:4x EDT)

This is written BEFORE any run on the panel below.  The ledger entries are L-129 (the 0-byte student) and L-137 (this).

## Where this comes from (development panel 901–964, already seen)
- `distill_fo_prefix_s0` is DAgger-distilled from the full-information teacher set_full_s0 (`scripts/MARL_e3_actor_distill_v2.py
  --student-delivery prefix --student-adapter freshonly`, 500 iterations).  It sees only the prefix packets decoded this
  step (fresh-only set receiver).
- Under the prefix (188.7 B/step) it gives:
  - −2.1 % [−3.0, −1.1] vs the 0-byte student distill_none_s0;
  - −2.0 % vs FO (the teacher with fresh-only messages);
  - −5.2 % vs set_none_s0.
- Cap 4 (100 B/step) gives −2.0 % vs the 0-byte student.
- One arm, one seed.  It was designed after seeing L-129 (the student beats FO).

## Hypothesis
Inside the PACKET protocol HETERO_v0 (unchanged: K_i ~ U{1..7}, 25 B payloads, prefix stream), training-time
communication (a full-information teacher) and deployment messages (fresh only) combine.  Such a student beats the best
0-byte policy.

## Arms and seeds
- Student `distill_fo_prefix_s s` for s ∈ {0, 1}; s = 1 is distilled from set_full_s1 (training since 23:4x).
- Comparator (PRIMARY): the 0-byte student `distill_none_s s` distilled from the same teacher (s = 1 is training).
- Secondary: set_none_s s; maxq; the byte-budget variant (set_full_s s, 3 B, 27 B/step); the student under cap 4.

## Panel
- **Traffic seeds 2201–2264 × headways 8 / 16** (128 episodes), checked unused for any E3 episode at 23:4x.
- It is used once for this comparison.  Panels 2001–2064 and 2101–2164 are not reused.

## Pre-stated criterion
- **PRIMARY**, per seed s:
  - statistic: the ratio of summed waiting, student (prefix) / distill_none_s s (0 B), minus 1;
  - bootstrap over traffic seeds, both headways together, 4000 resamples;
  - the upper 95 % bound must be < 0.
- The hypothesis is supported only if BOTH seeds pass.
- Evaluators:
  - the student: `scripts/MARL_e3_delivery_eval_v6.py`, which reads adapter = freshonly from the checkpoint;
  - the 0-byte student: v6 with no messages.
  - Full per-step access audit in both.

## Not claimed
- This is not the reserved test (1301–1316 stays closed).
- One distillation recipe (DAgger, 500 iterations, beta 1 → 0 over the first half), not tuned.
