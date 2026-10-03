# Pre-specified test D: does mixture training repair the 4×4 K = 1 loss that no interface could repair?

Written 02/10/2026 15:1x EDT (`date` 15:16:27 before writing), BEFORE any run.  User 15:1x (queue D after the CPU-heavy jobs).
Source: 4×4 K = 1 reversal (L-270, −2.41 %; replicated −2.47 %, L-279), no interface repair (clip L-270, time projection L-279);
the culprit is a JOINT support violation (late low coverage, L-272); the 3×3 mixture covered its feasible set (L-256).

## Arms
relayMIX_st_s0–9 on the 4×4 grid: scripts/MARL_e3_actor_distill_v11.py --capacity mix (default regimes iid / const1 /
const2 / const3 = v10's) under MARL_grid_relay_wrapper (nearest8), teacher set_full_s<s> (4×4), the relayCage recipe
otherwise; watchdog without --out, --park-if-no-state.  Comparators: relayCage_st (iid-trained) and relayCK1_st (K = 1-trained,
PROTOCOL_E3_G4_TRAIN_MATCH) on 4×4, Z.  Panel 4601–4664 × 8/16 (unused, checked at launch); capacities K = 1, 2, 3, iid.
Started only after test C (queue).

## Predictions (fixed now; means over seeds 0–9)
- D1 (repair by training support): relayMIX vs Z at K = 1, mean ≥ 0 and lower bound > −0.5.
- D2 (no cost in the training regime): relayMIX vs relayCage at iid ≥ −0.5 %.
- D3 (minimax): relayMIX's worst gain over the four capacities exceeds relayCage's and relayCK1's.
Reading fixed now: D1 + D2 → on the second network too, a joint-support failure that no interface repairs is repaired by
widening the training support; D1 failing → the 4×4 K = 1 channel limits the value itself (information, not support).
