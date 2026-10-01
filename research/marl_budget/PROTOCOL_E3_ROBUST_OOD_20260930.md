# Out-of-distribution demand for the byte-budget designs (DEVELOPMENT-CONFIRM protocol, 30/09/2026, written 09:2x EDT)

This is written BEFORE any run on the panel below (a one-episode smoke test on seed 2501 checked only that the evaluator
runs).  The ledger entry is L-155.  The plan is in `research/papers/audits/MARL_NEW_DIRECTIONS_20260929.md` (P2).

## Question
Every actor was trained on mean headways 8 and 16 s only.  Do the two supported byte-budget designs still beat the 0-byte
distilled student when demand is heavier (6 s), in between (12 s) and lighter (24 s)?  The two designs are TRAINEDQ4
(3 B payloads in training) and BYTEBUDGET (eval-only compression).

## Arms (seeds 0 and 1; every checkpoint exists)
- TRAINEDQ4: set_fullq4_s s, eval v7 `--quant 4 --byte-capacity 3 --adapter-override freshonly --deliveries prefix`.
- BYTEBUDGET: set_full_s s, the same flags.
- Comparators:
  - distill_none_s s: v6, no messages; the PRIMARY comparator;
  - set_none_s s: v6, no messages;
  - maxq.

## Panel
- **Traffic seeds 2501–2564 × headways 6, 12, 24** (192 episodes per arm), checked unused at 09:2x.  Used once.

## Pre-stated criterion
- **PRIMARY**, per seed s, for TRAINEDQ4:
  - statistic: the ratio of summed waiting over all 192 episodes, arm / distill_none_s s, minus 1;
  - bootstrap over traffic seeds (all three headways of a seed together), 4000 resamples;
  - the upper 95 % bound must be < 0.
- TRAINEDQ4 is robust to this shift only if BOTH seeds pass.
- **Secondary**, reported as measured:
  - BYTEBUDGET with the same statistic;
  - each headway separately.  The pooled ratio is dominated by the heavy 6 s regime, so the per-headway numbers are part
    of the report;
  - vs set_none and vs maxq.

## Not claimed
- This is not the reserved test.
- The same 3×3 grid; other networks would need retraining (the actors' input is tied to 9 agents).
