# EXPLORATORY 4×4 development look (seed 0 only) at the channel-map predictions

Written 01/10/2026 18:59:49 EDT, before the runs below.  Only relayCage_st_s0 / distill_none_s0 / set_full_s0 of the 4×4
chain are complete.  Development episodes seed901–904 × 8/16 (NOT the pre-registered target panel 3301–3364 of
PROTOCOL_E3_G4_CONSTK_20261001, whose rules and Addenda 1–2 are unchanged and remain the confirmatory test).
Runs: Z rows; decision-level net_Z (scripts/MARL_e3_negflip_probe_v2.py) at const1–const6 and iid; closed-loop relay vs Z
(scripts/MARL_e3_ageclip_eval.py --A -1) at K = 1–6 and iid; all through the 16-agent wrappers.
Predictions (Addendum 2 and the channel map, e3_channel_composition_20261001/g4_*): R-abs → net_Z and gain negative at K = 1
and 2, positive from K = 3, with K = 4 at or below K = 3 (B_abs 2.65 vs 1.88); R-rel → no age-driven deficit at any K (B_rel ≤
1.2), so any K = 1 deficit is the coverage component (never-heard ×14.5 of training).  One seed, 8 episodes: direction only.
