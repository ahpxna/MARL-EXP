# EXPLORATORY cross-student test (artifact subagent H5): does a K = 1 decision probe certify congestion-order fragility?

Written 01/10/2026 19:46:05 EDT, before the runs.  Students with the probe's adapter (quant 4): relay6_st_s0–9 (trained under the
congestion order), relay6Clow_st_s0–1 (congestion order, low capacity), plus relay6Cage_st_s0–9 (existing e3_negflip_20261001).
Probe: scripts/MARL_e3_negflip_probe.py --K 1 (development seed901–904 × 8/16; teacher set_full_s<s>, Z distill_none_s<s>).
Outcome (already on disk, e3_overnight_report_20260930.json): congestion-order gain vs Z = −mean of the prefix/cap4 and
prefix/low effects.  Prediction: Spearman(net_Z(K = 1), congestion gain) over the 22 students ≥ 0.3 (kill if < 0.3); also reported
within relay6_st (10 seeds).
