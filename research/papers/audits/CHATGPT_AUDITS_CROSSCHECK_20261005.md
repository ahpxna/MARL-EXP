# Cross-check of the ChatGPT audit files against the current state (05/10, 00:27)

**Source:** all 27 files in `/Users/phanan/Documents/ChatGPT/CIG-AMF/research/catchup/` (03/10 00:25 … 04/10 23:25), read in full this session.

**Purpose:** list every demand that is still live for M3 / the methods paper, and mark each one:
- DONE (with its ledger row);
- QUEUED / BUILT;
- MISSING → added below as X-items in the night plan.

Historical demands that later rows already closed (B6, reward B, R8–R10, M2a fixes) are listed only by the row that closed them.

## 1. Map: user's list → file

| # | User's title | File |
|---|---|---|
| 1 | Literature, depth of reading, novelty gaps | METHOD_SEARCH_LITERATURE_20261004 |
| 2 | Eight hypotheses, pipeline, controls, budget, stopping rule | METHOD_HYPOTHESES_NIGHT_20261004 |
| 3 | M3 audit and the path to a method | M3_FAILURE_CAUSES_AND_METHOD_PATH_20261004 |
| 4 | Full audit and step-by-step worker guide | M3_M4_FINAL_AND_F1B_REVIEW_20261004, TWO_POPULATION_CAUSAL_DIAGNOSIS_20261004 |
| 5 | M3 results audit and next step | M3_DEV_FAILURE_REVIEW_AND_NEXT_STEP_20261004 |
| 6 | Checked report | M3_PROTOCOL_D1D76226_PRE_SCREEN_REVIEW_20261004 |
| 7 | M3 audit | M3_E_VS_COMMITMENT_AND_ORACLE_AUDIT_20261004 |
| 8 | M2b report | M3_E_VS_COMMITMENT_AND_ORACLE_AUDIT_20261004 §1 (the M2b audit) |
| 9 | Detailed M3 guide for the worker | M3_BEFORE_LAUNCH_REVIEW_20261004 |
| … | others | PAPER_READINESS_AND_HYPOTHESIS_LINEAGE, TWO_POPULATION_PAPER_FINISH_LINE, CITY_R8_R10_PROGRESS, SPAT_PILOT_REVIEW, CITY_B6_FINAL_AND_SPAT, PRELAUNCH, NEW_DIRECTION_RESEARCH, DESTINATION_AND_REOPENING, CORPUS_RECOMPOSITION, HISTORY_FRAMING, the 03/10 E3 files |

## 2. Live demands and their status

| Source § | Demand | Status |
|---|---|---|
| HYP §2 N1 | Exposure at the queries the fleet actually receives; an arm that only abstains in the tail | **DONE, REJECTED** (C-97): exposure 0.11 %; tail − all +0.01 % |
| HYP §2 N2 / LIT §1 | Direct movement-specific TTG with state; censoring explicit; episode split; same data / budget as age-only; no "sum of quantiles" | **BUILT, QUEUED** (job 030). The model is a small torch MLP quantile net, not boosted trees: sklearn is unavailable and nothing was installed. Censoring and the error breakdown are to be verified → X1, X2 |
| LIT §1 | The three provider limitations must be separated: (i) age-only conditioning; (ii) tail fallback; (iii) summed phase quantiles ≠ the quantile of TTG | (i) N2; (ii) N1 done; (iii) **MISSING as its own arm** → **X1** |
| HYP §2 N3 | Paired branches from one prefix, forecast computed in both, only one branch uses it; calibration under the service policy vs one-shot with the SAME total data | **TO BUILD** (job 040). Note LIT §2: closed-loop refit already exists (`CITY_m3_train_E.py:59`), so "refit" is not new; the test must be the specific component |
| HYP §2 N4 / §3 table | Service gate vs publish-all, P-tail, P-confidence, P-random / P-ETA at matched activation, A-no-feedback, A-no-receiver | **TO BUILD** (job 050). The plan lacked **A-no-receiver** (gate without the receiver-variation feature) → **X4** |
| HYP §2 N5 / §5 | Realized out-of-sample utility; sensitivity-only / cost-only / receiver+cost; situations are nested (not 96 independent); affected cohort is treatment-dependent; hindsight max is privileged | **TO RUN NOW** (offline). The H3 caveats are written in C-96. Chaos → compare with the situation's mean over options, not I0 → **X5** |
| HYP §2 N6 | Natural switch then announce vs forced switch now; Q-gap ≠ fuel regret | Partly answered by M3′-D F0 (C-95). The out-of-sample H3 split by RL-H action → in the N5 script |
| HYP §2 N7 | Many interventions in a full episode; exposure / penetration and group limits | After a candidate (job 060) |
| HYP §2 N8 / LIT S02–S03 | Learned cycle / split baseline on the same frozen fleet, TRAIN / SELECT and rights; not a new method | **TO BUILD** (job 070, CEM on TRAIN) |
| HYP §6 step 0 | Seeds from the registry; never reuse 450–549 as a final test | DEV 600–611 created after a non-existence check (N1 job). The spider DEV 100–109 was already used in M4 3b → labelled "DEV, already viewed" in C-97. Confirmation reserve 700–739 untouched |
| HYP §6 step 1 | Screen budget ≤ 96 episodes (2 lights × 2 fleets × 6 DEV × 4 arms); collection / fit cost reported separately | N1 used 12 DEV (192 + 40 episodes, 5 min); N2 reuses its R / c2 rows. Costs are logged per job |
| HYP §7–8 | Math only if a signal exists; paper conditions (baselines, ablation, replication, transfer, novelty vs FoRL / integrity gating / commitments / performative risk / SPaT forecasting, practicality costs) | Pending a candidate. The novelty table (04:51 list) must cite S01–S20 |
| FAIL §4.1–4.3 | RPC: forced hold, message withdrawal, blocked-decision logging | **DONE** (C-95; H1 log in RPC2) |
| FAIL §7 H4 / H5 | Reset std / value head; constrained fleet objective | Optional; F1-B stopped (C-94). H5 is the natural next reference if time remains → **X8** |
| FAIL §6 | α 0.025 is not chain-wide 0.05 (Bonferroni bound 0.075) | Recorded in PROTOCOL_CITY_F1B |
| FINAL §3 | Frontier figure: common denominator; F1 label; numeric codes; "cost–contribution comparison" | **DONE** (fig v2, C-88) |
| FINAL §7 | Seven manuscript sentences | **DONE** (C-88 errata); recheck at the next paper pass |
| FINAL §1 | Clean up dead processes by PID | **WAITING for the user's PID confirmation** (list given earlier) |
| DEV §2 | MAE ~1 s is measured on each arm's own queries; split the error by horizon, by yellow / green, and by the ticks where the policy actually commands | **MISSING** → **X2** (N2 compare and N1 offline get the breakdown) |
| DEV §2 | No CI was computed for the per-row fleet contributions | Paper-side; add CIs when the M3 table is rebuilt → **X9** |
| DEV §4 | All E arms saw the receiver features: "weighting ablation under the same information", not "policy-aware vs policy-free" | Check the paper wording → **X9** |
| PRESCREEN B6 / D-dir | D needs calibration of D's own output; h = 0 when the policy wants to switch | Historical (E pilot closed, C-67 / C-68) |
| EVC §2 | "Information-value ladder": exact / fc50 / fc20 / unavailable on the SAME replayed light trace and fleet | **MISSING** → **X3**. It also gives N3 a clean open-loop vs closed-loop contrast |
| EVC §2 | Oracle replay is not an upper bound | DONE (C-63) |
| BEFORE §3 | Minimum lead time: a promise known 1 s before green is useless | Covered by the lead-time logs of RPC2 / H3; the N4 gate must carry the horizon → in X4 |
| READINESS §4 A–G | M2a corrections: the "wrong forecast" label, commanded seconds INCOMPLETE, P-M2-3 NOT SUPPORTED, runner exit code, four pairs not factorial, DiD units, teleports | **DONE** (C-60) |
| CORPUS §5 H-PATH | Upgrade order: light-first vs fleet-first through (L0, F0) → (L1, F1); transient at a mid-episode swap | Not in the mandatory list → candidate for the 04:51 list → **X10** |
| NEWDIR §6–8 | Reverse direction (fleet upgraded, light frozen), observation adapter q_θ vs DC-Ada | Pre-SPaT branch, superseded by the M1 / M2 pivot. Listed for 04:51 only |
| PRELAUNCH 2 | Uncertainty axes light × fleet × traffic; 2 seeds per side is not enough for headlines | All N-series reports use the crossed bootstrap. Confirmation reserve: ≥ 5 lights / fleets |

## 3. Added to the night plan (X-items)

| ID | What | Why (source) | Cost / where |
|---|---|---|---|
| X1 | **(00:47) Structurally null on grid4:** every grid4 light has 2 greens + 2 fixed 3 s yellows, so a red link's TTG = the remaining time of ONE green + fixed yellows. Quantile of the sum = sum of quantiles (a constant shift), as LIT §1 itself notes. X1 matters only on spider (multi-phase); deferred there. Original item: **N2-sum arm**: age-only marginals, but TTG computed as the quantile of the SUM (Monte-Carlo joint draw of the remaining phase durations), not the sum of quantiles | Separates a wrong statistic from missing state (LIT §1 counterexample) | Offline error first (in the N2 compare); an endpoint arm only if offline MAE improves ≥ 10 % |
| X2 | Error breakdown by horizon bucket (0–5, 5–15, 15–30, > 30 s), by light state (green / yellow / red), and at commanded ticks only, for c2 / N2 / X1 | DEV §2 | Offline, in `CITY_n2_fit.py` compare |
| X3 | **Information-value ladder on a fixed light trace**: R's RL-H phases recorded, then replayed; the fleet receives exact / c2 q0.1 / N2 q0.5 / unavailable | EVC §2; also gives N3's open-loop arm | Queue, after 030: 2 k × 2 fleets × 6 DEV × 4 arms = 96 short episodes |
| X4 | N4 ablations: A-no-receiver (gate features without the receiver command variation), lead-time feature | HYP §3, BEFORE §3 | In job 050 |
| X5 | N5 / N6 chaos-aware estimand: chosen option minus the situation's mean over options; random-choice null; cluster bootstrap over the (k, seed) episode | C-96 reading | Offline now |
| X8 | Optional H5: Lagrangian agent-TL constraint for the retrained reference | FAIL §7, FINAL §6 | Only if the queue empties |
| X9 | Paper pass: E-arm information wording; CIs for the fleet-contribution rows | DEV §2, §4 | At the next manuscript pass |
| X10 | H-PATH upgrade order (FT / R10 → FT / F1-B → RL-H / F1-B vs the light-first path) | CORPUS §3.2, §5 | 04:51 candidate list |

## 4. What the audits say a methods paper still needs (unchanged)

The audits list five requirements:
1. a candidate that beats R within the limits;
2. it beats the strongest same-rights baseline (forecast / gate / commitment / cycle), with a positive ablation of the new component;
3. replication on fresh checkpoints and traffic;
4. transfer to one independent setting where the baselines and the learned fleet work;
5. novelty vs FoRL, integrity gating, probabilistic commitments, performative risk control, and SPaT forecasting, plus practicality costs.

None of these is met yet. N1 is rejected; the RPC family is closed as tested (C-95); H3's registered "YES" needs the out-of-sample test (C-96).
