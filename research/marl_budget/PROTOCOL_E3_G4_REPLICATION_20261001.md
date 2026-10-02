# Pre-specified replication on a SECOND NETWORK (4×4 grid): relay vs compiled silence, and the N_s predictive law

Written 01/10/2026 11:1x EDT, BEFORE any of the runs below (user 11:1x: "kill 20595 rồi chạy 4×4 luôn đi").  On the 4×4 grid
only seed 0's teacher and zero-byte student exist (30/09 phase 1); its relay students died with ENOSPC; seeds 1–9 have
nothing.  No 4×4 relay result exists, so nothing below has been seen.

## Arms (trained by the chain, same recipes as the 30/09 4×4 phases, smoke-tested then, ledger L-186)
For s = 0, …, 9 on the 4×4 grid (`scripts/MARL_grid_wrapper.py` / `MARL_grid_relay_wrapper.py --relay-slots nearest8`):
- teacher set_full_s (delivery v6, full delivery, 2000 iterations, set actor);
- zero-byte student distill_none_s (distillation from the teacher, no messages, 500 iterations);
- relay student relayCage_st_s (distill v6 from the teacher, relay age, 3 B codebook, 185-bit 25 B packets with the 8
  nearest agents per sender, AGE-FIRST order, 500 iterations).
Seed 0's existing teacher and zero-byte student are reused (COMPLETE manifests of 30/09).

## Predictor (development panel, computed by a fixed procedure; no tuning)
N_s = 1 − P(minset = 0) at ε = 0.25 from the V-D v1 probe (`scripts/MARL_e3_decision_depth_probe.py` under the relay
wrapper; cache base; age-first order; capacity low), on episodes seed901–seed932 × 8 / 16, with parity against relayCage_st_s's
own satrot rows on the same episodes (the 3×3 N_s definition, unchanged).  D_s = 1 − the last `agree` of distill_none_s's log.

## Target panel
Traffic seeds 2901–2964 × headways 8 and 16 s (128 episodes), used once; checked unused at 10:3x by parsing every
manifest's traffic seeds.  Conditions as PROTOCOL_E3_TEN_SEEDS_20260930: iid (rule prefix), cap4 (rule cap4, iid
capacities), low (rule prefix, low capacities); relay under age-first ordering; zero-byte student with no messages.

## Rules (fixed now)
- R1 (main effect on a second network): per condition, the mean over seeds of e_{s,c} = Σ waiting relay / Σ waiting Z − 1;
  two-level bootstrap (seeds, then traffic seeds within each), 4000 draws, seed 0; SUPPORTED iff the upper bound < 0 in all
  three conditions.
- R2 (the predictive law on a second network): gain_s = −mean_c e_{s,c}; SUPPORTED iff Spearman(N_s, gain_s) ≥ 0.5.
- R3: Spearman(N_s, gain_s) > Spearman(D_s, gain_s).
- Completeness: a seed whose training fails after the watchdog's retries is excluded and named; fewer than 8 complete seeds
  ⇒ INCOMPLETE (no verdict).  Reported regardless: per-seed effects, bytes, the 4×4 N_s values.
- Kill rule: if R2 fails, the N_s law is reported as specific to the 3×3 network and the flagship is downgraded to a
  single-network observation.

## Not changed after this file
Arms, recipes, predictor, panel, conditions, endpoint, R1–R3, completeness.  Report `scripts/MARL_e3_g4_replication_report.py`
is written before any target run.
