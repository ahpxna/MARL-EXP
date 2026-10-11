# Claim map: TSI methods paper (locked 05/10 ~08:0x; follows PAPER_FREEZE_ASSESSMENT_20261005)

**Rules:**
- Every claim in the manuscript must map to one row here.
- No row may be strengthened in the text.
- No new experiments for this paper (freeze).

## Primary (confirmation, registered)

| # | Claim (exact wording allowed) | Evidence | Protocol | Ledger |
|---|---|---|---|---|
| P1 | On grid4, TSI with per-light calibration reduces the frozen PPO fleet's fuel by 3.85 % (95 % CI [3.26, 4.43]), city TL by 0.55 and human TL by 0.89 s/veh vs R (RL-H + no SPaT), with agent TL non-inferior (−0.22, CI [−0.44, +0.04]; one-sided α = 0.025, margin +0.5); 0 teleports, 0 unfinished | `tsi2_20261005/report_tsi2_confirm.txt` | PROTOCOL_CITY_TSI2_20261005 | C-118 |
| P1-caveat | This is the SECOND registered attempt. The first (one global adapter) failed on agent TL (+0.85, upper +1.27). Both attempts use the same 5 light / 4 fleet checkpoints with fresh traffic; Bonferroni bound 0.075. t4–t7 also trained the F1-B fleets; the first attempt's per-light results motivated TSI-2's per-light calibration (C-128) | `tsi_20261005/report_tsi_confirm.txt` | PROTOCOL_CITY_TSI_20261005 | C-114, C-115 |

## Secondary (descriptive, same or fresh panels; TSI design frozen)

| # | Claim | Evidence | Ledger |
|---|---|---|---|
| S1 | Complementary halves on grid4: the service alone gives fuel −4.93 % but agent TL +1.97; the adapter alone gives fuel +0.29 %; neither alone meets the joint objective | report_tsi2_confirm (HYB, ADP2 rows) | C-118 |
| S2 | vs the repo's retraining recipe F1-B (same panel): no fuel difference detected (−0.68 % [−1.70, +0.11]; NOT an equivalence test); city / agent / human TL lower (−0.38 / −0.50 / −0.27, CIs exclude 0) | report_tsi2_confirm | C-118 |
| S3 | Demand +25 % (fresh 740–749): fuel −3.79 %, agent TL −0.27, all limits met | `shift_20261005/report_shift.txt` | C-120 |
| S4 | Receiver classes (fresh 750–759): rule R8 fuel −1.84 %; search R9 fuel −1.38 %; limits met (teleports checked afterwards from the saved rows: R9 3 / 100 runs = 0.03 per run vs R 0, within the limit; the GEN report itself did not check teleports, C-126) | `gen_20261005/report_gen.txt` (a); rows `gen_20261005/conf` | C-121, C-126 |
| S5 | Fleet share 25 %: fuel −4.13 %; agent TL one-sided upper **+0.4986** under the registered draws, but **+0.51 ± 0.01 across 40 bootstrap seeds (≥ +0.5 in 35 / 40): non-inferiority at the margin, NOT robustly shown** (C-128). 75 %: fuel −4.75 %, agent TL −0.58 (limits met) | report_gen (c); recomputation C-125, C-128 | C-121, C-128 |
| S6 | The age-only forecaster tried, with the same adapter, harms (+6.72 %); TSI is 9.87 points better. It does not replace the state forecaster in this design (no claim about every forecaster without state) | report_gen (b) | C-121 |
| S7 | Fleet-first upgrade under the old light is safe in this setting (F1-B fleets vs R10 under FT: fuel −2.23 %, agent TL +0.15) | report_gen (d) | C-121 |

## Mechanism (DEV / diagnostic; support a closed-loop account; no single mediator isolated)

| # | Claim | Evidence | Ledger |
|---|---|---|---|
| D1 | With SPaT, halting on served lanes falls (2.9 → 1.6) and RL-H's greens lengthen (14.8 → 16.9 s); agent TL rises, human TL falls | N2 rows | C-99 |
| D2 | Counting 0.1–2 m/s vehicles in front of the frozen light cuts the N2 agent-TL cost by 0.8 s/veh | `n2m_20261005/report_n2m.txt` | C-100 |
| D3 | On the light's recorded schedule replayed open loop, exact timing gives fuel −5.6 % and agent TL −0.37 | `n2m_20261005/report_x3.txt` | C-107 |
| D4 | Publishing shifts the target: ttg MAE 3.02 vs 1.70 s (shadow); scored waits > 30 s are 3.34 % vs 0.089 % of scored queries (queries, not vehicles) | `n3_20261005/report_n3.txt` | C-109, C-113 |
| D5 | The adapter (DEV, global q:2:0) reduces the publication sensitivity: MAE gap +0.73 vs +1.32 s, difference −0.59 [−0.88, −0.35]. Intervention evidence, not a loop-gain measurement or stability proof | `perf_20261005/report_perf.txt` | C-122 |
| D6 | Across the 5 confirmation lights (first attempt), the residual agent-TL cost grows with the residual green lengthening (descriptive, 5 points) | C-114 rows | C-117 |

## Negative / transfer failure (reported in full)

| # | Claim | Evidence | Ledger |
|---|---|---|---|
| F1 | Spider attempt 1: fuel −1.66 % [−1.99, −1.38]; city TL +0.55 (up +0.91) and agent TL +1.33 (up +1.94) FAIL; teleports 0.025 / run | `sptsi_20261005/report_sptsi.txt` | C-123 |
| F2 | Spider attempt 2 (α = 0.025): fuel −0.31 % [−0.81, +0.16] (no reduction shown); city +1.32, agent +1.43, human +1.20 FAIL | `sptsi_20261005/report_sptsi2.txt` (the header says "1110-1129"; the data are 1130–1149) | C-124 |
| F3 | On spider the service alone is strongly harmful (+20.7 % fuel, +59.5 s/veh agent); the adapter reduces that harm (−58.1 s/veh vs the service). This is relative to a very bad service, not a deployable result | report_sptsi | C-123 |
| F4 | Light-side commitments (WC5 +2.98 %, RPC +9.26 %), gates, tail abstention, CEM split control, and per-decision commitment selection are all worse than or no better than R | C-86, C-95, C-97, C-98, C-104, C-116 | — |

## Not claimed

- SOTA, or "first".
- Equivalence with retraining.
- Transfer of the method beyond grid4.
- That the two components are necessary for every method.
- Small-gain stability.
- That "97 %" means a deployment-relevant fraction.
- That hidden demand is the single isolated mediator.
- Non-inferiority at the 25 % fleet share (at the margin; bootstrap-seed sensitive, C-128).
- Any Blackwell-informativeness reading of the adapter (removed, C-128).

## Text-finishing log

- 09:00: Table 2 (`tab:allstats`) gathers every row P1, P1-caveat, S3–S5, F1, F2 under one convention; references verified (C-126).

## Wave 6 (PROTOCOL_CITY_WAVE6_20261005 + pre-run amendment; C-129)

| # | Claim (allowed wording) | Evidence | Ledger |
|---|---|---|---|
| W1 | TSI-2 met every limit again on a third fresh traffic panel 760–779: fuel −3.70 % [−4.24, −3.19], agent TL upper +0.10 (α 0.05). Same checkpoints: a fresh-TRAFFIC, not fresh-POLICY, replication | `w6_20261005/dca/report_dca.txt` | C-129 |
| W2 | A DC-Ada-STYLE affine adapter at matched budget (44 rollouts) accepted no candidate (identity = HYB). It missed the agent-TL limit (+1.98, upper +2.57) and is not ordered against TSI. It is NOT a faithful DC-Ada reproduction; no claim about DC-Ada | report_dca; amendment item 6 | C-129 |
| W3 | Retraining on 760–779: F1-B and H5 met the limits; H4 did not. TSI − F1-B fuel −0.60 [−1.57, +0.19] (post hoc; no difference detected, NOT equivalence); TSI's city / human TL lower | `w6_20261005/h45/report_h45.txt`; post-hoc computation C-129 | C-129 |
| W4 | The learned committed-duration light failed its DEV gate (city TL +2.04). Its reward was not normalised by the interval length (design flaw), so this is NOT evidence against learned predictable lights | `w6_20261005/lcd/report_lcd.txt` | C-129 |
| W5 | Swapping RL-H for a similar learned family (SIM-halt; a replacement, not an upgrade) did not change F1-B's benefit (DiD +0.01 [−0.25, +0.26]); one family only | `w6_20261005/m2l/report_m2l.txt` | C-129 |
| W6 | Spider attempt 3 (determined cells only) FAILED at α 0.0125: fuel +0.70 % | `w6_20261005/sp3/report_sp3.txt` | C-129 |

Added to "Not claimed":
- equality with F1-B on fuel (on either panel);
- a win over DC-Ada or any published method;
- fresh-policy replication;
- transfer to spider (three failed attempts).
