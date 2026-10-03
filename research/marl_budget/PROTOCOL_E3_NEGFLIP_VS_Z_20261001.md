# EXPLORATORY probe: decision flips of the relay student against the ACTUAL zero-byte student Z, and the age shift

Written 01/10/2026 11:58:37 EDT (`date`), after the prospective harm test (H1–H3 SUPPORTED, read 11:55) and its
comparators (Addendum 1).  EXPLORATORY: both target panels (2801, 3001) have been read.  Development panel only.

## Why (two gaps found while verifying the third external audit)
1. harm_S / net_S use the TEACHER on the local-only view as the baseline (net_S = acc_S − acc_E exactly), not the
   comparator Z.  On both panels net_S(1) = +0.092 > 0 while the realised gain(1) < 0: the decision-level measure has
   the wrong SIGN at K = 1.  The negative-flip rate against Z (correct-by-Z, wrong-by-relay; Yan et al. CVPR 2021)
   is the decomposition the audit's "repair minus corruption" story actually needs.
2. relay6Cage_st was trained under the iid capacity process (config capacity iid); constant K = 1 for every receiver
   and step changes the age distribution of relayed copies.  paper_marl_v2 §(training at low capacity) already
   reports that copies with an age distribution unlike training hurt.  So the K = 1 loss may be an age shift.

## System
As PROTOCOL_E3_PROTOCOL_CONDITIONED_DEMAND_20261001 (relay6Cage_st_s<s>, age-first, relay v2 merge, 3 B codebook,
seed901–904 × 8/16, seeds 0–9), K ∈ {1, 2, 3} constant and K = iid (the training capacity process).  Added per
receiver-step: zok = Z's argmax on the local-only view ∈ A_0.25; the number of entries and the ages (steps) of the
entries in the merged view the relay student reads.
SELF-CHECKS: Z acting from that local-only view in a no-delivery closed loop reproduces e3_dev_Z_20261001 rows
exactly (every development episode, every run); the identity net_S = acc_S − acc_E; the relay closed loop is the
protocol-demand probe's (same code path).

## Quantities
acc_Z = P(zok); repair_Z = P(¬zok ∧ protoS); flip_Z = P(zok ∧ ¬protoS); net_Z = acc_S − acc_Z = repair_Z − flip_Z.
Age: mean and 95th percentile of relayed-entry ages; share of receiver-steps with any entry older than the 95th
percentile of the iid run of the same seed.

## Expectations stated now
- X1 (decision level explains the sign): mean net_Z(1) < 0 < mean net_Z(2) and mean net_Z(3).
- X2 if X1 fails: the K = 1 loss is not visible as A_0.25 decision flips against Z; it is a closed-loop effect, and
  "communication corrupts decisions" is not the explanation at this resolution.
- X3 (age shift): the mean relayed age at const K = 1 exceeds that of the iid run on every seed, and flip_Z(1) is
  concentrated on receiver-steps with an entry older than the iid 95th percentile (rate ratio > 1.5).
- X4 (reported, no rule): Spearman of net_Z(K) and of flip_Z(K) with the realised gains of panels 2801 and 3001.
Probe `scripts/MARL_e3_negflip_probe.py`, report `scripts/MARL_e3_negflip_report.py`.
