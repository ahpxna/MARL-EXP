# Addendum 2 to PROTOCOL_E3_G4_REPLICATION_20261001: the decision-level negative-flip measure as a prospective predictor (R5)

Written 01/10/2026 12:24:22 EDT (`date`).  The 4×4 chain is still training (no 4×4 student finished; the target directory
research/marl_budget/e3_g4_replication_20261001 holds no run).  Trigger: the 3×3 exploratory probe against Z
(PROTOCOL_E3_NEGFLIP_VS_Z_20261001: net_Z has the sign of the realised gain at K = 1, 2, 3 and iid; K = 1 cross-seed
Spearman +0.709 / +0.673).  Nothing in the protocol or Addendum 1 is changed; one secondary rule is added.

## Added measurement
net_Z_s(c) = P(relayCage_st_s's executed action ∈ A_0.25) − P(distill_none_s's action on the local-only view ∈ A_0.25), on
the relay student's own closed-loop states of seed901–904 × 8 / 16 under capacity process c ∈ {iid, low} (the target
cells' processes), teacher set_full_s's full fresh view defining A_0.25.  Probe: the negative-flip probe run through
scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 (a capacity option is added in a new
version of the probe; its self-checks — Z parity at every step against a 4×4 Z development run, queue parity — must
pass).  Computed for every seed BEFORE the 4×4 replication report is read.

## Added rule (secondary; reported with N_s and margin)
- R5a: for each of iid and low, the sign of the mean net_Z equals the sign of the mean realised gain (R vs Z).
- R5b: Spearman(net_Z_s(low), gain_s(low)) ≥ 0.5 over the complete seeds.
Same-state decision effect (states from the relay's closed loop), not a whole-trajectory difference.
