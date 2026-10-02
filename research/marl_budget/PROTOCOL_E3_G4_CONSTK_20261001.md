# Pre-specified test on the 4×4 grid: does the constant-K sign reversal, its staleness signature and the age-interface repair replicate?

Written 01/10/2026 12:40:15 EDT (`date`).  No 4×4 replication student has finished training; no run below exists.
Source: the 3×3 chain (const K = 1 loss on three panels, −1.65 / −1.45 / −1.70 %; net_Z sign = gain sign at K = 1, 2, 3, iid;
tail staleness burden B_stale 8.48 / 1.64 / 0 / 0 at K = 1 / 2 / 3 / iid; age-clip +0.79 % [+0.05, +1.55] at K = 1, harmless
at iid).  PROTOCOL_E3_G4_REPLICATION_20261001 and its addenda are unchanged (they test iid / cap4 / low on panel 2901–2964).

## Arms (every 4×4 seed whose set_full, distill_none and relayCage_st checkpoints are COMPLETE; ≥ 8 seeds required)
relayCage_st_s<s> (age-first, nearest8 relay slots, iid-trained), distill_none_s<s> (Z), all through the 16-agent wrappers.
Development (seed901–904 × 8/16, before any target run of that seed): Z rows; scripts/MARL_e3_negflip_probe_v2.py at
const1 / const2 / const3 / iid (net_Z); scripts/MARL_e3_viewstats_probe.py at K = 1, 2, 3, 0 (composition; B_stale with
the threshold a99 = 99th percentile of the maximum copy age under iid, per seed); clip threshold a95_s = 95th percentile of
the maximum copy age under iid for seed s (integer steps).
Target panel: traffic seeds 3301–3364 × 8/16 (checked unused 12:39), used once.  R_none(K) = scripts/MARL_e3_ageclip_eval.py
--A -1 at K ∈ {1, 2, 3, iid}; R_clip(1) = --A a95_s at const K = 1; Z = scripts/MARL_e3_delivery_eval_v6.py.  Endpoint and
two-level bootstrap as PROTOCOL_E3_AGECLIP_PROSPECTIVE_20261001.

## Rules
- G1 sign reversal: at const K = 1, R_none vs Z mean gain < 0 with bootstrap upper bound < 0.
- G2 dose: mean gain(1) < gain(2) < gain(3), and development B_stale(1) > B_stale(2) > B_stale(3).
- G3 decision-level sign: sign of the mean development net_Z(K) = sign of the mean target gain(K) for K = 1, 2, 3, iid.
- G4 interface repair: at const K = 1, R_clip vs R_none mean > 0 with bootstrap lower bound > 0 (R_clip vs Z reported).
- Reported prediction (no rule): the 4×4 K = 1 burden exceeds 3×3's (8.48) and its loss is larger than 3×3's.
Interpretation: G1 + G3 → the phenomenon and its decision-level signature replicate on a second network; G2 → dose-response
in staleness burden; G4 → the age-interface part replicates.  Failure of G1 → the K = 1 reversal is 3×3-specific.
Launcher `scripts/RUN_marl_g4_constk.sh`, report `scripts/MARL_e3_g4_constk_report.py`, both written before the runs.
