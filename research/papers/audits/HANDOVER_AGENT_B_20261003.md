# Handover and acceptance report — subagent B (acae5606e7dd259e7), 03/10/2026 02:4x → 17:4x EDT
Received 17:5x; recorded by the coordinator (content as delivered, lightly condensed; numbers unchanged).

## Summary
* Delivered and copied into the repo: G1/G3 verification, train × deploy matrix, draft figures F1–F5, G5 design, Related Work + Results
  draft, protocol-vs-code audit.  NOT done: the PCT / dissonance receiver fine-tune design (cut off by the usage limit at 14:4x).
* Corrections pending before submission: E3 has no Bayes floor (the E3 split is a matched-training contrast); flips measure disagreement
  with the teacher, not wrong actions; F5 lacks MASK, the Mahalanobis gates and the joint throttle, and its panels are not paired;
  "minimax", "co-production" (as a result) and "Base+DR = delay randomisation" must go.
* Mahalanobis (L-301) final: neither detector dominates; F5 and the repair table must show benefit retained AND harm blocked, per cell.

## (1) Tasks
| Wake / time | Task | Status | Artefacts (repo) | Verification |
|---|---|---|---|---|
| Wake 1, 02:4x | G1 paired split (4201, 3201, 3801, C0); G3 on C0 exact tables | DONE | research/marl_budget/e3_train_deploy_matrix_20261003/g1_g3_wake1/ | split identity ≤ 1.8e-15 (by construction); 4×4 = stored report; 3201 recomputed independently by the coordinator; C0 exact vs panel Spearman 0.993 / Pearson 1.000 (33 cells); NOVELTY Add. 2, C-9 |
| Wake 2, 03:4x | Train × deploy matrix (17 panels) + flip / accuracy matrix | DONE | research/marl_budget/e3_train_deploy_matrix_20261003/ (matrix.json sha ecd6265b…) | equals stored reports on 16 panels; 896 manifests PASS; 632 sha = current; L-298 |
| Wake 3, 04:4x / 07:4x | Figures F1–F5 | DONE as drafts; F2 / F3 / F5 need revision | research/papers/_figures/paper1_draft_20261003/ | recomputation = reports; RI Bayes 0.6191 / 0.2231; 425 manifests PASS, 415 sha match |
| Day 10:3x | G5 protocol draft (city) | DONE (draft) | used for C-10; research/city_sim/g5_gate0_20261003/ | Gate 0: greens ≤ 19 s without the fleet; Gate 0b: τ > 50 on ACT80 0.84 % → low power |
| Day 12:4x | Related Work + Results draft | DONE (draft), wording fixes needed | research/papers/audits/PAPER1_DRAFT_RELATED_RESULTS_20261003.md | every number carries a ledger / note ID |
| Day 13:4x | Audit protocols vs scoring code + self-checks | DONE | L-300 | no printed verdict changed; fixes applied by the coordinator |
| Day 14:4x | PCT / dissonance fine-tune design | NOT DONE | — | state below |

PCT state: only the docstring chain of scripts/MARL_e3_actor_distill_v11.py (l. 1–60) was read (v11 = v10 + --mix-regimes; v10 = v9 +
--capacity mix; v9 = exact resume; v7 const⟨k⟩; v6 relay-v2 merge; v1 teacher on the counterfactual full view).  Tentative, NOT verified:
teacher logits are computed during distillation, so a teacher-A_0.25 mask is free at training time; the old CK1 receiver's action on new
states costs one extra forward pass.  To do: loss lines (l. 60–285), init-from-checkpoint option, RUN scripts / logs timing (L-250 ≈ 42 min
for 500 v9 iterations on 3×3; L-257 4×4 ≈ 4.4 s / iteration at load ≈ 6); predictions (NFR via the flip probe; gain at K1 and iid).

## (2) Delivered numbers / wordings needing correction or caveats
* E3 G1 split (+0.22 / −9.57 4×4; +0.83 / −2.94 3201; +0.72 / −2.78 3801; excess < 0 in 20/20 pairs): matched-training reference
  contrasts, NOT a Bayes decomposition (L-302(2)); proxy vs C0 exact floor Spearman 0.33, wrong sign on 2 / 9 lights.  No "excess risk" /
  "no information loss" claims for E3; the exact split exists only in RI.
* C0 split: built on c0_v3 whose producer cannot be verified (C-9) — secondary evidence with that caveat, or rerun frozen.
* FB6: +0.46 / +0.83 (order-broken ranks) → +0.50 / +0.88 (average ranks), verdicts unchanged (L-300).
* Matrix: "diagonal best 30/30" counts the same 5–10 checkpoints re-evaluated on many panels — not independent replications; pooled cells
  mix seed sets; K1 / iid cells pool more panels than K2 / K3; F1's 4×4 cells include test D (≤ 0.16 from the README).
* F1: one primary paired panel per receiver set; pooled cells to the supplement with the pooling rule.
* F2: split into (a) RI exact Bayes decomposition and (b) E3 matched-training contrast, relabelled; C0 to the supplement unless provenance is
  closed; each panel names its unit (ΔMSE / Δregret / −Δgain).
* F3: retitle "disagreement with the teacher's A_0.25 set on Z-driven states"; drop the mirrored downgrade row (NF(A→B) = PF(B→A)); same
  wording for "≈ 12 % / 4–5 %" in the draft.
* F4: report the per-seed sign of iid − K1 or Spearman instead of "rising on k / n seeds".
* F5: add MASK (5201: 4×4 CK1 −14.87 [−26.83, −7.02], iid-trained −15.30; 3×3 −4.07 / −4.55), the Mahalanobis gates, THR (5201: −14.52 at
  iid vs PLAIN −3.37); separate runtime interventions (PLAIN, LAB, EMU, THR, MASK, FB_S, FB_M*) from retraining (matched, MIX) with costs;
  label EMU "per-slot emulation adapter (partial: 1 108 050 of 3 612 970 below-floor entries had no older copy at 4×4 iid)"; the current
  bars come from 4 different panels (5101, 4901, 4601, 5201) and are not paired — say so or rebuild on one panel (P1).
* Draft text: RDC DR = delay-reconciled critic; Base 110.2 / 135.2 / 125.4 at delays 0 / 3 / 6, 142.3 is Base+DR at 6; narrow R2 to RI;
  drop "minimax" (D2 −0.52 % at iid); "an input-only throttle failed"; co-production is a HYPOTHESIS; remove "iff", "receiver-only repair
  impossible", "FB_S beats the standard gate".
* G5: Gate 0 assumed ACT's max green binds under human traffic; it does not; the 50 s support is created by the fleet (C-10); low power.
* EM4 holds by construction (L-300) — not evidence.

## (3) Mahalanobis (L-301) — presentation per cell (RELAY = frozen receiver; harm blocked = (gate − RELAY)/(−RELAY) where RELAY < 0;
## benefit retained = gate / RELAY where RELAY > 0; always the fallback rate)
4×4, panel 4901, 10 seeds:
| Cell | RELAY | FB_S (rate) | FB_M (rate) | FB_Mq (rate) |
|---|---|---|---|---|
| CK1 K1 (own) | +5.71 [4.24, 7.04] | +5.71 (0.00) | +5.74 (0.15) | +5.72 (0.04) |
| CK1 K2 | +2.04 [−1.16, 4.48] | −0.42 (0.96) | 0.00 (1.00) | −0.42 (0.96) |
| CK1 K3 | +2.02 [0.26, 3.81] | 0.00 (1.00) | 0.00 (1.00) | 0.00 (1.00) |
| CK1 iid (upgrade hazard) | −3.78 [−6.56, −0.94] | −0.01 (0.99) | 0.00 (1.00) | −0.01 (0.99) |
| Cage K1 (downgrade hazard) | −2.75 [−4.31, −1.23] | 0.00 (0.96) | 0.00 (1.00) | −1.79 [−3.10, −0.61] (0.69) |
| Cage K2 | +2.22 [0.97, 3.6] | −0.43 (0.92) | 0.00 (1.00) | +0.23 (0.67) |
| Cage K3 | +5.19 [4.0, 6.34] | 0.00 (0.92) | +4.16 (0.25) | +5.19 (0.00) |
| Cage iid (own) | +6.07 [5.05, 7.12] | +5.86 (0.05) | +5.74 (0.08) | +5.99 (0.01) |
Arithmetic summary (not a registered statistic): harm blocked in the two harm cells (−6.53) FB_S 99.8 %, FB_M 100 %, FB_Mq 72 %; benefit
retained in the four positive non-own cells (+11.47) FB_S < 0 %, FB_M 36 %, FB_Mq 44 %.  3×3 (4801): no upgrade-hazard cell; 6Cage K1
(−2.36): FB_S −0.12, FB_M 0.00, FB_Mq −0.62; own-cell retention ≥ 0.95 for every gate.  Caveats: FB_S's key has the time bin, the
Mahalanobis feature does not; FB_Mq's floating tie (false alarm 0–3.85 %); both to close in P1.

## (4) Provenance gaps and primary panels
Gaps: C0 producer unverifiable (C-9); no checkpoint sha in any Z manifest (incl. the 10 test-D Z); no relay sha on 2801 (CKPT_SHA256.txt
matches 10/10), 3001, 3601, 2901; reserved panel 2701 (L-201) mtimes only; the same checkpoints are re-evaluated on many panels.  All other
recorded relay sha equal the current files (632 + 415).
| Claim | Primary panel | Notes |
|---|---|---|
| Relay clears Z | 4×4 4201 (Cage iid +6.02, sha) | 3×3: 2701 reserved (sha gap) or 3801 |
| Upgrade hazard | 4×4 4201, GTM3, 10 seeds | 3×3 3201 TM / P-UP2 |
| Downgrade / K1 reversal | 4×4 3301, G1 | 3×3 2801 frontier |
| Matched rescue | 4201 (GTM1/2) | 3201 (TM1/2) |
| Mixture | 4×4 4601 (D1–D3; Z no sha) | 3×3 3801 (MX1–MX4) |
| Information split | RI ri_age_role_20261002/results.json (sha = current) | E3 contrast on 4201, labelled proxy |
| Rule A | 3301, Addendum 4 | — |
| FB3 / detectors | 4901 | — |
| Flips | dev episodes 901–904 | diagnostic |
| Silence bar | 5201 | — |
| Repair table | none paired today → P1 | — |

## (5) Next steps (review P0–P6)
* P0: claim map from §4 (claim, primary panel, rows path, producer hash, actor / eval seeds, comparator, CI, theorem conditions); apply §2
  wording; mark re-evaluated checkpoints as non-independent.
* P1: one shared distance function (vector = view form, scalar-equivalence test, deterministic tie rule); detector features with and
  without the time bin (FB_S± / FB_M±); freeze, then ONE new 4×4 panel (10 seeds; K ∈ {1, iid, 2, 3}) with every arm paired: Z, PLAIN,
  MASK, FB_S, FB_M, FB_Mq (fixed), EMU, THR, matched Cage, MIX; per cell gain, harm blocked, benefit retained, fallback rate,
  compute / memory, retraining cost; old rows kept in legacy.
* P2: the current THR is input-only (MARL_e3_joint_throttle_eval.py l. 102 `prev = mv`; the sender-side mirror follows the unthrottled
  stream).  (a) trace-level logs on dev episodes (sender selection, accepted packets, scheduler cache / mirror, timestamps, actions);
  (b) one coordinated intervention — the receiver's accepted history drives its relayed table (prev[i] = shadow view), the age mirror
  updates only on accepted packets, the shadow cache replaces the environment cache; (c) compare with the K1 run and plain-upgraded runs on
  the same seeds; (d) replay check when the iid deliveries contain the K1 packets; pre-register view parity, action agreement with K1,
  closed-loop gain; if it fails, co-production stays a hypothesis.
* P5: regenerate F1–F5 from the repo scripts with the §2 changes; F5 from the P1 panel.  P6: add environment and seed lists.
* PCT baseline: resume the design (v11 l. 60–285, RUN / log timings); predictions NFR via the flip probe and gain at K1 / iid vs matched
  and MIX; confound: fine-tuning on iid may lose K1 performance.
