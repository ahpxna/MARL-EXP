# Pre-specified test: PROJECTION into the training support, not TRANSPORT, repairs an upgrade (relayCK1 at richer channels)

Written 02/10/2026 12:4x EDT (`date` 12:43:58 before writing), BEFORE any run below (only a one-episode development smoke of
the evaluator: identity at K = 1 with parity, 719 projected entries at iid; no gain looked at).  User 12:3x: "phải làm gì với
thông tin của bước 1?"  Source: L-266 (transporting the age marginal to the training histogram hurt both directions by
4–7 %, the clip — a minimal projection — helped +0.69 %) and L-263 (testbed: minimal emulation > full emulation).

## Hypothesis
A learned receiver is hurt by deployment views outside its training SUPPORT; the repair that works moves each view as little
as possible into the support.  For relayCK1 (trained at const K = 1) every individual age at iid (0–2) is inside its training
ages (0–8), but the view's FRESH COUNT is not: under K = 1 exactly one entry per step is fresh (the prefix head), under iid
1–7 are.  Projection "onefresh" (scripts/MARL_e3_projection_eval.py): keep age 0 only for the direct entry whose sender is
first in the public committed order; show every other direct entry one step old (the smallest move making the fresh count
1).  Content, relayed entries and protocol state unchanged.  This is NOT distribution matching: the age marginal stays far
from the K = 1 histogram.

## Design
Panel 4101–4164 × 8/16 (checked unused 11:43 by parsing every manifest / config, and at 12:43 by grep), used once; seeds 0–4.
Cells: relayCK1 plain at K = 1, 2, 3, iid; relayCK1 onefresh at K = 2, 3, iid; identity check relayCK1 onefresh at K = 1 with
parity to its plain rows; relay6Cage plain at iid (the retrained iid specialist); Z.  Endpoint, pairing, two-level
bootstrap as PROTOCOL_E3_TRAIN_MATCH_K1.  The age-remap effect of L-266 (−5.21 % at iid, panel 4001) is the transport
comparator (another panel: reported, not tested).

## Predictions (fixed now; mean over seeds 0–4)
- SP1 (projection repairs the upgrade): relayCK1 onefresh vs plain at iid > 0 with bootstrap lower bound > 0.
- SP2: onefresh ≥ plain at K = 2 and K = 3.
- SP3 (exploratory): relayCK1 onefresh at iid ≥ relayCK1 plain at K = 1 (the projected richer channel beats the emulated
  training channel because the relayed copies stay fresher).
- Reported: recovery fraction (onefresh − plain) / (relay6Cage plain − relayCK1 plain) at iid.
Reading fixed now: SP1 → the upgrade hazard of this receiver lives in a joint support statistic (the fresh count), and the
minimal projection repairs it where transport of the age marginal failed — "projection, not transport" holds in both
directions (clip for downgrades); SP1 failing → the fresh count is not the culprit (another support statistic is).
Launcher scripts/RUN_marl_e3_support_projection.sh and report scripts/MARL_e3_support_projection_report.py written before.
