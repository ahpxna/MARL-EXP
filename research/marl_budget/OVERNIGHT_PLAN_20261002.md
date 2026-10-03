# Overnight plan (user 02/10/2026 01:0x EDT) — read at every 30-minute check-in, update the status column

User request: analyse the 4×4 results so far and show what can be shown on localhost; do E1, E2, E3, E5; wake up to start
E4 when those are done and the CPU is free; afterwards wake once more to optimise and restart the 4×4 chain; check every
30 minutes and report progress, trends, what they mean, good or bad, and predictions WITH their basis; audit; research.

| Item | What | Status | Notes |
|---|---|---|---|
| TM seed 4 | relayCK1_st_s4 with v9 (Deviation 1) + 6 evals + TM report | DONE 01:43 (L-250): TM1, TM2, TM4, P-UP1, P-UP2 SUPPORTED, 5 seeds; no stall | verify manifests + report before stating TM1–TM4 |
| Arch control | AC1–AC3 (attention / shared-concat) | DONE 01:53 (L-252): AC1 generic for attention AND shared-concat; AC2 not → compatibility failure, architecture-general | report waiter bzxg264kg |
| 4×4 analysis + localhost | dashboard + CityFlow replays | DONE (L-247): dashboard localhost:8766 (refresh: scripts/MAKE_e3_dashboard.py); replays localhost:8767 | |
| E2 | volatility-weighted count | DONE (L-244: no gain, cv 0.08) | |
| E3 | heterogeneous budgets, channel-only net | DONE (L-246): E3a hit; slack belongs to the hub order | |
| E5 | per-student pre-deployment robustness score | DONE (L-246): dev net_Z at K=1 ρ +0.794; training-state probes ≈ 0 | |
| E1 | both-sided mismatch law (PROTOCOL_E3_MISMATCH_LAW_20261002, panel 3701–3764) | DONE 01:38 (L-249): ML1, ML2, ML4 SUPPORTED; ML3 NOT (crossing at K≈2) | 36 evals, one lane, ≈ 45 min; report auto |
| E4 | mixed-channel training (PROTOCOL_E3_MIXED_CHANNEL, v10 = v9 + mix) | DONE 03:58 (L-256): MX1, MX2, MX4 SUPPORTED; MX3 NOT (specialist +1.05 at K=1) | panel 3801–3864 |
| 4×4 relaunch | optimised resumable launcher; resume set_full_s5/s7/s9 in place; v9 students; fewer lanes; skip complete actors | RUNNING since 03:59:37 (L-254, PROTOCOL_E3_G4_RELAUNCH_20261002): scheduler pid 72761 (nohup, --cores 10), log research/marl_budget/g4_relaunch_20261002/scheduler.log, waiter b1xs3x446; NO target statistic before the reports; dedupe automatic | stopped 01:0x (L-245) |
| W1 prospective | relayCK2 (const K = 2) test of the frozen W1 law (PROTOCOL_E3_W1_PROSPECTIVE_20261002) | ARMED: starts when the 4×4 scheduler exits (waiter bg2nhycfn); report auto | L-259 |
| Audit + research | audit every claim/result of the night; then research | ongoing (L-258, L-259; MARL_COMPAT_MECHANISM_20261002.md) | |

CPU free = no training process running for TM / arch control / E-runs and 1-minute load < 12.
Disk: at every check-in, if free < 25 GB run `scripts/UTIL_dedupe_hardlink.py --log research/marl_budget/dedupe_hardlink_20261002.jsonl research/marl_budget legacy` (hard links only; finished runs only).
