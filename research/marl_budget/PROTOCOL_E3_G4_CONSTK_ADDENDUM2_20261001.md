# Addendum 2 to PROTOCOL_E3_G4_CONSTK_20261001: competing channel-only predictions for the 4×4 cells (written before any 4×4 const-K run)

Written 01/10/2026 18:46:52 EDT (`date`).  No 4×4 const-K run exists (e3_g4_constk_20261001 absent; the 4×4 chain is still
training).  New fact computed today (scripts/MARL_e3_channel_composition_probe.py, development episodes seed901–904 × 8/16,
relayCage_st_s0 on 4×4 and relay6Cage_st_s0 on 3×3; outputs research/marl_budget/e3_channel_composition_20261001/, sha256
d70496a9… (4×4) and 60478208… (3×3)): at constant K the merged-view composition is set by the channel schedule alone (the
3×3 probe reproduces the multi-seed view statistics exactly: B_3 8.48 / 1.64 / 0 / 0, never-heard 1.13 / 0.54 / 0.29 / 0.18).
On 4×4 the IID TRAINING PROCESS ITSELF has a long age tail (maximum copy age p99 = 9 steps vs 3 on 3×3):

| 4×4 | B_3 = E[Σ(a−3)+] | B_9 = E[Σ(a−9)+] (τ = iid p99) | max age p50 / p95 | never-heard |
|---|---|---|---|---|
| K = 1 | 17.35 | 1.20 | 9 / 12 | 6.57 |
| K = 2 | 16.41 | 1.03 | 9 / 14 | 2.07 |
| K = 3 | 1.88 | 0 | 4 / 6 | 2.49 |
| iid | 0.54 | 0.02 | 2 / 6 | 0.45 |

## Two readings, fixed now, with opposite predictions
- R-rel (the failure is exposure beyond the policy's OWN training range; the reading G5 already uses, τ_s = iid p99):
  every 4×4 B_τ ≤ 1.2 < b* = 3.7 ⇒ NO age-driven sign reversal at any K; K = 2 gain > 0.
- R-abs (the failure is absolute staleness, τ = 3 as on 3×3): B_3(1), B_3(2) > 3.7 ⇒ reversal at K = 1 AND K = 2; K = 3 gain > 0.
- Coverage: never-heard at K = 1 is 6.57 vs 0.45 under training (3×3: 1.13 vs 0.18), so a K = 1 reversal is expected under
  either reading if the sparse-coverage component is material; it does not discriminate.
- DISCRIMINATING CELL: 4×4 const K = 2.  Gain(2) < 0 with bootstrap upper bound < 0 ⇒ R-abs; gain(2) > 0 with lower bound > 0
  ⇒ R-rel; otherwise undetermined.  Reported with G1–G5; no other rule changes.
