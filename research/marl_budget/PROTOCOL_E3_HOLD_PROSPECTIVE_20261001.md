# Pre-specified PROSPECTIVE test: a schedule-only increase of the stale tail removes the communication gain at fixed K

Written 01/10/2026 19:22:31 EDT, BEFORE any run on the panel below.  Source: the exploratory development dose
(PROTOCOL_E3_HOLD_DOSE_20261001; e3_hold_dose_report_20261001.txt: K = 2 gain +1.32 / −0.07 / +0.79 / −0.42 / −0.24 % at hold
r = 1 / 2 / 3 / 4 / 6, K = 3 +1.39 / +0.78 / +0.53 % at r = 1 / 4 / 6; Spearman(B_3, gain) −0.833 over 9 cells).
## Design
Panel traffic seeds 3501–3564 × 8/16 (checked unused 19:22; maximum used 3464), used once.  Seeds 0–9.  Z
(scripts/MARL_e3_delivery_eval_v6.py) and relay6Cage_st_s<s> under models/marl_delivery_hold.HoldDelivery(r)
(scripts/MARL_e3_hold_eval.py --A -1) at (K = 2, r ∈ {1, 3, 4, 6}) and (K = 3, r ∈ {1, 6}).  Channel-only B_3 of the cells:
1.64 / 5.31 / 8.10 / 11.95 and 0 / 5.95.  Same bytes and fresh count within K.  Endpoint and two-level bootstrap as before.
## Rules
- HD1 dose within K = 2: relay(r = 4) vs relay(r = 1) mean < 0 with bootstrap upper bound < 0.
- HD2 reversal by schedule alone: relay(K = 2, r = 4) vs Z mean gain < 0.
- HD3 dose across cells: Spearman(B_3, mean gain vs Z) over the six cells ≤ −0.6.
- HD4 fragility: Spearman over seeds of gain(K = 2, r = 4) vs Z with the mean const-K = 1 gain over panels 2801 / 3001 / 3101
  ≥ 0.5 (the per-student trait of L-220).
Interpretation: HD1–HD3 → the stale tail CAUSES the loss of communication value at fixed capacity, bytes and fresh count
(the schedule is the only change); HD4 → the same per-student fragility governs schedule- and capacity-induced shifts.
Launcher scripts/RUN_marl_e3_hold_prospective.sh, report scripts/MARL_e3_hold_prospective_report.py, both written before the runs.
