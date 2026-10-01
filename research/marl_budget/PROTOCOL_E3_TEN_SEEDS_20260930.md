# Pre-specified test: relay under age-first ordering against compiled silence, ten teacher/student pairs

Written 30/09/2026 20:18 EDT, BEFORE any run on the panel (ledger L-186).  Panel checked unused (no manifest in
research/marl_budget contains any traffic seed in 2701–2764).

## Panel
Traffic seeds 2701–2764 × headways 8 and 16 s (128 episodes), used once.  Development choices were made on 901–964.

## Arms (all already trained; no training on this panel)
- **Primary:** relay6Cage_st_s0 … s9 (relay students trained under age-first ordering, 185-bit layout, saturated ages),
  evaluated under age-first ordering.  Evaluator `scripts/MARL_e3_delivery_eval_relay_satrot.py --relay age --quant 4
  --order agefirst`.  Conditions: iid (rule prefix), cap4 (rule cap4, iid capacities), low (rule prefix, low capacities).
- **Comparator:** distill_none_s0 … s9 (the same-seed zero-byte students), evaluator `MARL_e3_delivery_eval_v6.py
  --deliveries none`.
- **Secondary:**
  - the same relay students under the congestion order;
  - the replicate zero-byte students distill_none_rep_s0 … s9 where trained;
  - BYTEBUDGET reference not run.

## Endpoint and rule (primary)
- For each condition c and seed s, the paired effect is e_{s,c} = (Σ waiting relay)/(Σ waiting zero-byte) − 1 over the
  128 episodes.
- The primary statistic per condition is the mean over the ten seeds of e_{s,c}.
- Its 95 % interval comes from a two-level bootstrap: resample the ten seeds with replacement, then traffic seeds
  (both headways together) within each, 4000 draws, generator seed 0.
- **Rule:** SUPPORTED iff the upper bound is below zero in all three conditions (an intersection–union test; each
  one-sided at 2.5 %).
- Otherwise NOT SUPPORTED, and every number is reported as measured.

## Secondary readings (reported, not part of the rule)
- Per-seed effects with traffic-seed intervals.
- Spearman correlation between e_{s,·} (mean over conditions) and the teacher headroom H_s (BYTEBUDGET vs zero-byte
  student, development, L-160/L-170).  Predicted ≥ 0.5 (L-185 found 0.84 on development).
- Relay under the congestion order: predicted to lose its advantage at low capacity for some seeds.
- Against the replicate zero-byte students, where available.

## Not changed after this file
Arms, conditions, panel, endpoint, bootstrap and rule.  The report script implements exactly this file.
