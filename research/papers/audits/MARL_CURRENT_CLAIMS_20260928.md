# MARL — CURRENT claim map (single current truth; 28/09/2026, updated about 13:17 after the self-audit)

- This file supersedes every claim table in `MARL_CRITICAL_PATH_STATUS_20260927.md`. The sections of
  that file dated before 28/09 12:25 are HISTORICAL.
- Written per `MARL_FINISH_HANDOFF_20260928.md` F0.
- **Goal, unchanged:** a MARL method paper. Its selector must show an incremental benefit under fair
  resource accounting.
- **Not a goal:** "MAPPO beats max pressure" is not a selector contribution. A negative result does not
  by itself switch the goal to an analysis paper; that is the author's decision.

**Actor seeds and gates.**
- BC recipe (BC from MP2 + MAPPO, `PROTOCOL_E3_PILOT`):
  - Rule: the gate is read on the pilot seed s0 for the chain's selector results.
  - G1 per seed: s0 FAIL, s1 PASS, s2 PASS (+3.0% [+0.9, +5.2], 15:01), s3 PASS, s4 PASS. Pass rate 4/5; the pilot fails.
  - Under the protocol, the BC chain's selector results are **not read as a method result**.
- Scratch recipe (MAPPO from scratch, `PROTOCOL_E3_SCRATCH`):
  - Rule: the gate is read per seed.
  - ALL FIVE PASS G1 and G2 (16:54; the replicas in `e3_scratch_rs_20260928` for s0/s1/s2/s4, the run of record by the pre-declared rule). None vs actual: s0 +4.3% [+1.5, +6.6], s1 +6.3% [+4.2, +8.5], s2 +7.9% [+5.6, +9.9], s3 +7.3%, s4 +8.7% [+6.4, +11.0] (seed-cluster CIs). Pass rate 5/5. Selector results so far: s3 only; the downstream for s0/1/2/4 runs (another session's `RUN_marl_e3_resume_v4.sh`).
  - A result on a gated subgroup is conditional on the gate.
- Mixed-profile actor (`PROTOCOL_E3_MIXACTOR`): seed 3 training, a pilot.

## Claims

**Theory**

| # | claim | comparator / object | evidence | seeds / split | source | status |
|---|---|---|---|---|---|---|
| T1 | Deployable regret ≤ 2(δ+u)(d−R)₊ + 2ε + ν + ζ | abstract set function | LEAN | — | `LeanMarlEstimatedRevisionV1` (full9) | proved, CONDITIONAL on its hypotheses. **F5 bridge v2** (about 13:17; v1's "hTop false 16/16" is WITHDRAWN, self-audit L-01..L-04, L-34), 16 reduced actor-realised subproblems per actor (scratch s3, BC s3):
  - η_top = η* (the prefix is top-k at the SMALLEST constant) in 5/16 and 5/16; at η_top EVERY state has a valid
    ScoreLocal + hTop instance (16/16). The scores are fitted after seeing the full table: a reduced-object numerical
    instantiation, not a deployable certificate (independent recheck; L-36);
  - η_top has median 7.0 / 6.0, about the value spread (9.6 / 8.5);
  - the optimum is within one revision in 15/16 and 13/16;
  - the valid bound 2η_top(d−R)₊ holds everywhere: 0 where d ≤ R, 2.8 / 3.29 / 6 / 6.67 × the loss in the 4 nonzero states;
  - bytes cost 0 and coverage costs little.
  SINGLE-receiver scope: consistent with an estimation bottleneck; the multi-receiver decomposition (F5b) is the
  test for selectors that edit several receivers |
| T2 | Per-receiver block frontier; zero price at a 2η margin | abstract | LEAN | — | `LeanMarlBlockFrontierV1` | proved, conditional (hTop, ScoreLocal); unchecked in traffic |
| T3 | Calibration cost of ambiguous repairs (needle class) | Gaussian channel | LEAN + NUM (E1a) | — | `LeanMarlRepairCalibrationV1` | proved for the class; E1a is consistent with it |
| T4 | Argmax of an estimate with per-value error ε loses ≤ 2ε (sharp); edit-if-gain > 2ε never loses; every threshold τ < 2ε can harm (`threshold_sharp`, 13:13) | abstract | LEAN | — | `LeanMarlSafeEditV1` (smokeSafeEdit2_20260928, 7 theorems) | proved. **Not instantiated:** no valid pointwise ε for the learned critic; q90 quantiles are diagnostics |

**Fixed-MP2 actor**

| # | claim | comparator / object | evidence | seeds / split | source | status |
|---|---|---|---|---|---|---|
| M1 | A 1 B response bid helps a direct selector in the held phase | ctrl_history, same bytes | NUM, preregistered | test 601–616 | B2 | PASS: +1.85 [+0.95, +2.84], 18% of the oracle |
| M2 | ... and in closed loop | retrained ctrl | NUM, preregistered | test 801–816 | B4 | PASS against the retrained control only; −0.68% against the prefix (n.s.); 4.5% of the oracle |

**Learned actors**

| # | claim | comparator / object | evidence | seeds / split | source | status |
|---|---|---|---|---|---|---|
| A1 | Actor competence | MP2, same communication | NUM, development | BC s0–s4, scratch s0–s4, mix s3; dev 501–508 | msguse | every finished actor (11) beats MP2 by 9.5–24%: BC +9.5% to +14.0%, scratch +17.6% to +24.2%, mix +22.4% (BC s2 +12.4%; CI > 0). **This is not a selector result**. Seeds 3–4 are outside the protocol seed lists but were launched before any result (L-25) |
| A2 | The actor uses messages | same actor: none / stale / shuffle | NUM, development | same | msguse | 9 of 11 finished actors pass G1 (none worse by +3.0% to +17.5%): all 5 scratch and BC s1–s4. BC s0 (the pilot) and the mix actor do not. Mix: none −0.9% [−2.3, +0.6], stale +7.5% [+5.7, +9.5], shuffle +4.9%, full −1.9% n.s. (seed clusters). 'none' is an INPUT ablation, not a zero-byte deployment |
| A3 | Robustness of the actor's advantage | MP2 under a held-out load and bursty capacities | NUM, pilot panel | BC s0, s3 | frontier/shift | MP2 is +13% to +26% worse |
| A4 | Delayed receiver observations (stress test, idealised scheduler) | same actor at d = 0; MP2 at the same d | NUM, pilot panel | scratch s3, BC s3 | `e3_delay_20260928` | the scratch actor loses 3.9% / 5.6% at 20 s / 30 s; the gap to MP2 narrows to about 9%. **NOT a network-delay test of the method** |

**Selectors on learned actors**

| # | claim | comparator / object | evidence | seeds / split | source | status |
|---|---|---|---|---|---|---|
| S1 | A legal selector improves a learned actor | same actor + prefix | NUM, development and pilot panel | scratch s3 (gated); BC s0 and s3 recorded | ablation, frontier, diag v2 | **NOT supported so far.** Scratch s3: every variant ≈ 0 (n.s.). BC: +2% to +4% WORSE at caps ≥ +56; BC s1 ablation (+84, recorded): every variant +2.45% to +4.13% WORSE (CI > 0). Pair-order accuracy (tie-half, diag v3 / ranking v2; the old strict 0.40–0.48 is WITHDRAWN) 0.48–0.52 on DEV, at chance: legal 0.495 [0.482, 0.509] scratch, 0.526 [0.486, 0.567] BC; in-sample TRAIN 0.65–0.67 (generalisation gap, cause not isolated); harm given an edit 0.43–0.75, against an oracle headroom of +15.4 per state |
| S2 | The paid response bid (vs no bid) | sel_bid vs sel_nobid; with and without head | NUM, development | scratch s3 | ablation | no closed-loop effect (−0.36% n.s.). The bid raises the head's recall 0.006 → 0.15 |
| S3 | Response bid vs a SAME-BYTE alternative (queue) bid | queue bid, 10 B, same code (selector v4) | NUM, development | scratch s3, BC s3 | `selectors_v4`, `e3_dev_arms.json` | no bid helps on either actor. Top-2 / queue / none: −0.35 / −0.85 / −0.43 (scratch) and −1.03 / −1.49 / −1.04 (BC). Top-2 − queue +0.49 and +0.45, n.s. |
| S4 | R1 vs direct | same evaluator and candidates | NUM, development | MP2 track (direct_indep); E3 scratch s3 | — | direct ≥ R1 on MP2. On E3 both ≈ 0. R1 is an analysis object unless it wins on resources |
| S5 | Learned SchedNet-style adaptation (frozen actor, 1 B weights) vs the committed prefix | same actor | NUM, pilot panel | scratch s3, BC s3 × 3 init seeds | `e3_schednet_v2` | adaptation worse by +0.4% to +4.8% (2/6 significant). An adaptation, not a reproduction of the original SchedNet (no encoder or actor co-training). Float-score training, 1 B deployment |
| S6 | Label acquisition: targeted vs uniform vs singleton | same budget B = 24 (checked: no state short), legal bins (v2) | NUM, development | scratch s3, BC s3 | `acquisition_v2/` | no strategy helps on either actor (all means ≤ −0.19; BC s3 all ≤ −1.2). v1 (full gap) is kept as privileged acquisition. Registered but not yet run: the same on the dense labels (L-32) |
| S9 | Where a MULTI-receiver selector loses (F5b, added 14:24) | family of the labels + multi-receiver rollout local search (diagnostic) | NUM, development | scratch s3, BC s3 (48/48 each; final 15:15) | `e3_mrdecomp_20260928/report_v2.json` (v1 `report.json` kept) | **corrected 16:2x (independent recheck 16:11, N1/N2; self-audit L-47, L-48).**
  - Best found = max of both searches per state: +20.75 / +16.29 (v1 said +20.1 / +16.0, family-start search only).
  - Coverage outside the family ≥ +5.31 / +3.96 (a lower bound).
  - R1 inside the family +2.7 / +2.5 (inside the family only); bytes ≈ 0.1.
  - The legal selector's within-family SELECTION REGRET is +15.63 / +13.65 = ranking loss of the critic's argmax (+15.24 / +14.17) + signed threshold effect (+0.38 [−2.14, 3.08] / −0.53 [−1.29, 0.29], seed CIs, n.s.). The threshold changes 69% / 24% of the choices, so ν ≠ 0. This is estimation plus the decision rule, not 2ε alone. With no threshold the argmax realises ≤ +0.44 for every checkpoint.
  - A local search from the prefix reaches 84.7% / 84.7% of the best found (not 88% / 86%), with ~2.5 swaps on ~2.5 receivers.
  - Superadditive in 22/40 and 19/38 states.
  - So the tested legal rules fail to extract the headroom, mostly because the critic ranks candidates badly; geometry and coverage are NOT zero; this does not prove that all global regret is estimation |
| S7 | Prefix-trained vs mixed-trained actor | same selectors | — | mix s3 | — | G1 FAIL (16:54): its selector results are diagnostic only. Mix vs scratch s3 on paired dev episodes: +0.57% [−1.77, +3.07], no advantage and no shown equivalence. Actor COMPLETE (15:36): best select 1352 (scratch s3 1316, MP2 1730), no hang. The downstream (`RUN_marl_e3_mix_downstream.sh`) was launched at 15:36: message use, labels v3, selectors v1/v2/v3, closed loop |
| S8 | Is response information the bottleneck? (F2-A) | legal vs privileged-joint evaluator, same labels | NUM, development, diagnostic | scratch s3 | `selectors_v3` | partly. Privileged-only − legal is +2.12 [+0.10, +4.49] on scratch s3, but **n.s. when clustered by traffic seed** ([−0.21, +4.56], L-05). On BC s3 it is +2.79 [+1.02, +4.73] (seed-clustered [+1.11, +4.68]). The privileged evaluator realises only about 12% of the oracle gain. **F2-B, the legal multi-class head, is NEGATIVE on both actors**: −0.60 and +0.41 vs legal, both n.s., while privileged − multi is +2.72 and +2.38 (CI > 0). No closed loop (the rule: only if development improves) |

## What is open, in order (handoff §4)

1. **F1.** The dense-label round: original vs dense on the same state intersection, then the full
   dense development panel.
2. **F2.** The privileged-joint diagnostic (running). A multi-class response model only if it is
   supported. The mixed-actor pilot is running.
3. **F3.** Same-byte queue-bid data on TRAIN/SELECT/DEV; the baseline set is fixed before the freeze.
4. **F4.** Acquisition v2 (legal bins, provenance, budget assert). Delay kept as a stress test
   (scope (i)) with a causality assertion.
5. **F5.** A reduced, fully enumerable bridge panel (η on the whole small space, and the loss
   decomposition).
6. **F6.** The final protocol and freeze, then seeds 1301–1316 exactly once.
7. **F7.** The manuscript: Methodology with two recipes, Limitations, related work (NDQ, CASEC,
   M2I2, MUTE, Dense Coverage), figures separating the actor from the selector.

**If F1 and F2 stay negative:** the method-scope condition is NOT met, and this will be reported
plainly. Falling back to analysis + empirical limits is for the author to approve.
