# Handover and acceptance report — subagent A (a5e043f5fc399c33b), 03/10/2026 02:4x → 17:4x EDT
Received 17:5x; recorded by the coordinator (content as delivered, condensed; numbers unchanged).

## Bottom line
* Five of six tasks DONE; the sixth (paper-1 theory section draft) NOT DONE — cut off by the usage limit before any file was written.
* Three deliveries contained errors later corrected from the PDFs: RDC "Base ≈ 125 at delay 0", a misleading CALF framing, SIL-C /
  Calibrate-your-listeners figures taken from summaries.
* LeanMarlFrozenFloorV1, LeanMarlTaskVsReconV1 and LeanCityReceiverContractV1 are compiled and in verify_all.sh but NOT smoke-gated.
* One docstring paragraph of LeanMarlFrozenFloorV1 overstated L-296 → fixed by the coordinator 17:5x (L-303).

## 1. Tasks
| Wake | Task | Status | Recorded in |
|---|---|---|---|
| 02:4x | Deep read: CGDC, Decoupled DC, CALF, Shisher–Sun (2208.06948v2, 2404.16281), Bansal, SIL-C, contract shielding | DONE, mostly from WebFetch summaries | LITERATURE_DEEP_READ (per paper, threats, baselines) |
| 03:4x | G7 floors separation + Lean candidates L1–L3 + what E3 may claim; W3 Yan 2021, Shen 2020, Srivastava 2020, Lee 2019, Lu 2020 | DONE | G7_FLOORS_SCOPE_20261003; LITERATURE wake-2 |
| 04:4x → 07:4x | Standard comm-MARL benchmark survey; found the RDC anticipation | DONE | LITERATURE wake-3; NOVELTY Addendum 3 |
| 10:3x → 12:4x | Lean L2 LeanMarlFrozenFloorV1 (+ L1 LeanMarlTaskVsReconV1) | DONE (rc 0, no sorry, standard axioms; re-compiled by the coordinator) | L-299; verify_all.sh MODS l. 134 |
| 13:4x | [VERIFY] items from PDFs (SIL-C, Wang 2021, Lu 2020, Bansal, DACOM, RDC) | DONE | NOVELTY Addendum 4; draft corrections block |
| 14:4x | Paper-1 theory section draft | NOT DONE | skeleton in §5 below |

## 2. Evidence level and errors
* Verified from primary text (PDF pages, 13:4x): SIL-C Eq. 4 gate, Eq. 8 fallback, Table 1; Wang 2021 Table 1 (98 / 94 / 37 / 36) and the
  over-confidence sentence; Lu 2020 App. C Table 2 (R1 21.9 → 9.7 ± 1.2); Bansal 2019 §5.1 sentence, Fig. 2, 150 cycles / update at 75 /
  80 → 85 %; DACOM method, delay model, benchmarks, baselines; RDC §5 (DR definition), §5.2 sentence, Table 2 p. 17, Table 4 p. 18, Table 6.
  Wake 3: IC3Net pp. 5–8, 11–14 ("under 12 hours on 16 cores", TJ success, 2000 epochs); MAGIC pp. 5–8.
* PDF pages read at the time but not retained — RE-CHECK before printing: PCT NFR 6.44 → 2.35 (error 30.29 → 30.47); BCT 0.0 %, 80.25, gain
  26 / 65 %; Srivastava BTC 94.5 ± 1.31, OCR 55 → 86.4 %; Lee BLEU values.
* Summary only: CGDC, Decoupled DC, CALF tables, Shisher–Sun Lemma 3 / Thm 3(b), 2404.16281, contract shielding, MUSCLE, Lazaridou 2020,
  CoDe; repo pages (MAGIC, IC3Net, RDC-pymarl, JaxMARL), MPE2 docs.  Plot only: Wang 2021 30-listener ≈ 75 % (Fig. 3a).  Inference: RDC
  training ranges 3–9 (MPE) and 0–6 (SMAC) from Table 2 delay_value / delay_scope.
* Errors and status: (1) RDC "Base ≈ 125 at delay 0" — 125.4 is Base at delay 6, Base at 0 is 110.2 (corrected 13:4x); the coordinator's
  Addendum 4 then gave 142.3 to Base — it is Base+DR (L-302, Addendum 5).  (2) DR = delay-reconciled critic, not delay randomisation; the
  0–2 drop is a support argument on MPE only (SMAC: 0–2 inside training, no drop).  (3) CALF 476 vs 495 compares two DIFFERENT policies;
  every CALF policy improves as its own channel improves → no frozen-receiver upgrade hazard; CALF numbers are from a summary.  (4) SIL-C
  like-for-like is PTGM + AA +2.6 → +18.6 and 0.0 → +42.5.  (5) Wang ≈ 75 %, not 80 %.  (6) Lu R1 is in a table.  (7) simple_reference is
  NOT a safe negative control (reviewer P3); CPU-hours unverified.  (8) "Lemma 3 presumes full support" is an interpretation from a summary.

## 3. Lean status
| Module | Compiled | verify_all.sh | Smoke gate |
|---|---|---|---|
| ReceiverFloorV1, V2, PrefixInstanceV1 | yes | yes | PASS smokeMARLFLOOR (L-235) |
| NetFloorV1 | yes | yes | PASS smokeMARLNET (L-242) |
| EmulationV1 | yes | yes | PASS smokeMARLEMU (L-262) |
| ProvisioningV1, SupportV1, HoldFloorV1, MixtureV1 | yes | yes | PASS smokeMARLVERIFIED (L-264) |
| MismatchW1V1 | yes | yes | PASS smokeMARLW1 (L-260) |
| DecisionDepthV1, CommValueV1 | yes | yes (added L-299) | PASS work/gate_runs/smokeMARLDD3_20261001 (29 modules, 205 audited theorems) |
| FrozenFloorV1, TaskVsReconV1 | yes (L-299) | yes | NOT smoke-gated |
| CityReceiverContractV1 | yes | yes (added L-299) | NOT smoke-gated |
No full gate (full10 stopped 33/315, L-280).  Sufficient / one-direction / single-example results: emulation_repairs and
emulation_keeps_training_optimum (sufficient, not iff; hpush not shown for any E3 garbling); task_upward_closed and identify_implies_decide
(one direction); provisioning (caps a knowledge count; no sign prediction); receiver_floor / net_floor / burden_floor (knowledge upper
bounds; equality only on witnesses); upgrade_emulation (decode-set inclusion, not equality of laws); single finite examples:
upgrade_hazard, frozen_floor_not_monotone, marginal_match_insufficient, no_receiver_free_certificate, order1_blind_pair,
order2_blind_triple, task_lt_reconstruction (m = 3).  Not in Lean: the RI exact Bayes decomposition (Python check only), the dynamic task
floor L3, any closed-loop / return statement, mixture age response.

## 4. Open literature items
CGDC App. E.4 zero-delay numbers and code; Shisher–Sun exact Lemma 3 / Thm 3(b) on the PDF; CALF Tables 4–5 on the PDF; Decoupled DC
details; contract shielding §5.3 numbers; Bansal AAAI-2019 long version (N); MUSCLE, Lazaridou full texts; wake-2 PDF numbers (Yan, Shen,
Srivastava, Lee) before printing; RDC seeds per setting, inferred training ranges, RDC-pymarl licence; benchmark last-commit dates, MPE2
licence, CPU-hours, SC2 on this Mac, NDQ's TarMAC reimplementation.  Protocol versioning between learned agents: nothing found (3 searches).

## 5. Next steps (review P0–P6)
P0 theory rows of the claim map (wording proposals):
| Claim | Lean | Scope | Gate | Empirical link ("consistent with") |
|---|---|---|---|---|
| Knowledge floor: no scheduler lets a receiver know more than Σ_{s<n} K*(s) recent measurements | ReceiverFloorV2.receiver_floor; PrefixInstanceV1.prefix_receiver_floor; ReceiverFloorV1.timed_forced_stale | full-relay knowledge model; knowledge, not decisions | smoke | stale tail at constant K |
| Channel cap behind rule A | ProvisioningV1.provisioning; NetFloorV1.net_floor | constant K; t ≥ τ+1; cap only | smoke | rule A prospective (C-rel 3/3) |
| A training-optimal frozen receiver can be worse than silence on a Blackwell-dominating channel, task floor met on both | SupportV1.upgrade_hazard; FrozenFloorV1.frozen_floor_not_monotone | one finite example, fixed laws, one-step risk | SupportV1 smoke; FrozenFloor compiled only | upgrade hazard (L-298 28/29, 10/10) |
| Sufficient condition for emulation (hpush, hsem) | FrozenFloorV1.emulation_repairs | sufficient only; open loop; hpush not shown in E3 | compiled only | EM2 consistent; EM1 / JT1 do not test hpush |
| Marginal matching is not enough | FrozenFloorV1.marginal_match_insufficient | one finite example | compiled only | per-slot EMU hurting at K2 / K3; FB_S works at the joint level |
| No certificate from the two channel laws alone | CityReceiverContractV1.no_receiver_free_certificate | one example | compiled only | motivates receiver-relative monitors (L-293, L-301) |
| Deciding can need fewer decoded senders than identifying | TaskVsReconV1.task_lt_reconstruction; identify_implies_decide | static, noiseless, m = 3 | compiled only | scope note: knowledge floors are not decision floors |
Words to drop: "decision floor", "iff", "minimax", "exact E3 decomposition", "receiver-only repair impossible", "forced staleness causes the
failure", "first to observe the upgrade hazard".
P1: use the SIL-C definition for the standard detector (diagonal Gaussian prototypes, √χ²_0.99, verified Eq. 4); state FB_Mq's form and
its measured 0–3.85 % false alarm.  P2: hpush is the formal target of the coordinated intervention; pre-register replay of the K1 view
JOINT distribution from trace logs as the success criterion before any closed-loop run.  P3: MPE2 with message-level delay after a pilot;
minimum anchor = replicate RDC Base at d ∈ {0, 3} on TAG (110.2 vs 135.2).  P4: main text — frozen-receiver counterexample, sufficient
emulation result (+ marginal_match_insufficient), knowledge floor / rule A cap; appendix — T1, task_lt_reconstruction, bayes_refine,
DecisionDepth, HoldFloor, Mixture, MismatchW1; smoke-gate FrozenFloorV1, TaskVsReconV1, CityReceiverContractV1 before citing; present the
RI decomposition as a computation; every theorem says "fixed input distributions, open loop".  Statements NOT grounded in a compiled
module: dynamic task floor, any age → decision / return bound, the RI decomposition as a theorem, hpush in E3, "joint support is the
cause", rule A sign / sufficiency, mixture age response, every closed-loop statement.
