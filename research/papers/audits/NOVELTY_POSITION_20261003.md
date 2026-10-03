# Novelty and position of the current direction, after a fresh literature search (03/10/2026 00:15 EDT)

User 00:1x: "phân tích novelty của hướng hiện tại đi, research lại rồi phân tích vị trí hiện tại".  Searched 00:0x–00:15
(standard web search, abstracts / landing pages; no subagents).  Earlier verified neighbours (CITY_TWO_POPULATION_NOVELTY
§2, §6, §7; MARL_CORPUS_LEDGER_NOTES_20260930; MARL_LESSONS_AND_STORY_20261002 §2) are reused, not re-verified.

## New neighbours found today
| Work | What it does | Bearing on us |
|---|---|---|
| CGDC, arXiv 2604.03785 (2026) | delayed-communication POMG; message effect = communication gain − delay cost; value-loss bound by an information gap between timely and delayed message-induced action distributions | closest THEORY neighbour of E3's "communication value vs staleness"; their bound is about delay, ours about training support; must be cited and contrasted |
| Decoupled Delay Compensation, arXiv 2605.26286 (2026) | policies trained synchronous degrade under delays; a learned transition model + Kalman layer replaces delayed messages by current-state estimates, no retraining | an INPUT-side repair that WORKS — consistent with our H1 (it restores the conditional law of the current state; age relabelling did not) |
| Rainbow Delay Compensation (NeurIPS 2025), DACOM (2022), CoDe (AAAI 2025), CALF (arXiv 2603.12543, network-aware training) | delay-aware MARL training / fusion; training under realistic network models closes deployment gaps | "train at the deployment channel / under randomised channels" is KNOWN (≈ our train-match and mixture) |
| Shisher & Sun, MobiHoc 2022 ("How does data freshness affect real-time supervised learning?") | inference error is a possibly NON-MONOTONE function of AoI (when data are far from Markovian) | "fresher is not always better" is known for a single learned predictor; their cause is the data process, ours is the receiver's training support — must be cited and separated |
| CTDS (2022), PTDE (2022), CTEDD (2019), DDCA, CoDiMAD, KD-MARL (2026), MAGPO (2025); Communication-Enhanced Tutoring (2025) | distil a centralised / communicating teacher into communication-free students; the last compares distillation against communication | the compiled-silent student exists as a METHOD; our use of it as the mandatory BAR for runtime communication is a methodological stance, not an invention |
| Fastap (PMLR 216, 2023), SRPO (arXiv 2602.21515, 2026), MEAL continual MARL benchmark (2025) | teammate policy changes / partner shift; adaptation or risk-averse training for cross-play | partner-shift robustness is an active area; none certifies a partner upgrade before deployment from logs |
| CoTV (2022), signal–vehicle cooperative RL, integrated routing + TSC (ORNL) | lights and CAVs trained JOINTLY | joint training only; no independently updated pairs |
| Flow zero-shot transfer to a scaled city (arXiv 1812.06120) | noise injection helps sim-to-real transfer of AV policies | robust-training precedent for the fleet side |
| Patents on V2X application-version coordination (e.g. US 12054167 B2, US 2022/0300267) | industry already treats version mismatch between connected vehicles / infrastructure as a deployment problem | practical motivation for compatibility certification (cite as motivation only) |

## Claim-by-claim verdict
### MARL / E3 ("support, not freshness")
| Claim | Closest prior | Verdict | Our evidence |
|---|---|---|---|
| E1 runtime communication must beat a same-teacher compiled-silent student | CTDS / PTDE / distillation lines; Tutoring 2025 | methodological stance; partially anticipated | strong (many designs fail the bar: L-105, FO, HETERO variants) |
| E2 relay + age-first beats that bar under capacity limits | Gama 2012.14906, NeurComm; max-age-first AoI scheduling | mechanism known; the measured result under the bar is ours (incremental) | strong (10-seed reserved panel; 4×4) |
| E3 UPGRADE hazard: a receiver trained on a staler channel LOSES on a fresher one; the K = 1 reversal of the iid-trained receiver | delay-MARL papers report only the downgrade direction; Shisher–Sun: non-monotone AoI error from the data process | **not found as such — the strongest novel empirical claim**, provided Shisher–Sun is cited and the mechanism (training support) is shown — which E3 does (train-match rescue, mixture, support diagnostics) | strong: 3×3 many panels, 4×4 10/10 seeds, RI testbed |
| E4 support, not distance / freshness; prospective channel-side rule A; double dissociation | Johansson–Sontag–Ranganath 2019 (support in domain adaptation); AoI theory | application to channel–receiver compatibility with a prospective, channel-side rule and Lean floors: **new in combination** (moderate) | moderate–strong (L-270 C-rel 3/3, L-277, L-272); NYC pending |
| E5 input-side repairs fail; matched / mixture training repairs; support fallback | CALF, Rainbow DC (robust training known); Decoupled DC (an input repair that works); Simplex / OOD fallback | repairs by training are known; "relabelling in-range inputs fails" is new as an observation but must be stated with H1 (decision-sufficient edits such as current-state estimation work); fallback is standard | strong for the failures (4 interface repairs); fallback running (#3) |
| E6 Lean: receiver floor, provisioning, support hazard, mixture bound | — | formal artefacts; small but distinctive | compiled clean; full gate not re-run |

### City ("receiver-relative backward compatibility of independently updated learned agents")
| Claim | Closest prior | Verdict | Our evidence |
|---|---|---|---|
| C1 eco-driving harms sensing lights (Q2) | Stevanovic et al. TRR 2013; SPaT-uncertainty eco-driving | **known** — motivation only | robust in SUMO (Q2b) |
| C2 U-shaped age of vehicle-carried information (Q3) | VANET information-propagation literature (not searched this round) | likely known in shape; needs a search before any claim | single setting |
| C3 a genuinely better learned light breaks an independently trained learned fleet; a compatible mode repairs (Q7) | Bansal 2019; SIL-C 2025; Fastap; ZSC cross-play; CoTV (joint) | general principle known; **this traffic instance with two independent learners not found**; the "compatible mode" equals the engineering max-green, so the contribution is choosing it from the receiver's support | **weak: one training seed** (Q7b replication running) |
| C4 partner-only certificates cannot be universal (T1, Lean) and a receiver contract (region + exposure + behaviour, H2b) is needed | assume-guarantee contracts (AAAI 2024 / 2025, 2026 shielding); industry version matrices | impossibility is simple; the receiver-contract certificate for learned partners is a **candidate** contribution, untested (Q7b B3) | Lean T1 clean; Q7-3 failure; Q7b smoke hint (closed loop) |
| C5 compatibility may need interaction order ≥ 2 or 3 (T3, Q4) | t-way interaction testing (Kuhn & Wallace), k-wise independence, Helly-type | formal content classical; the reading for frozen learned receivers is new but small | Lean T3 clean; Q4 (s = 2) in a toy corridor |
| C6 commitment windows have a real price (Q5) | SPaT / commitment literature | negative result, minor | one valid demand level |

## Position (where we stand)
1. **MARL E3 is the mature paper.**  Its defensible novelty is narrow and specific: the upgrade direction of the training-
   channel hazard for learned communication receivers, explained by training support (not freshness or distance), predicted
   channel-side (rule A) and repaired by changing the support, all under a compiled-silence bar.  Its main threats are the
   delay-MARL papers ("just train at the deployment channel" — CALF) and Shisher–Sun ("fresher is not always better").  The
   answer to both is already in our data (the hazard's direction, the rescue by matching / mixture, the support diagnostics),
   but the manuscript (paper_marl_v2.tex, "Fresh Coverage …") predates all of it and must be rewritten around it.
2. **The city track is a promising framing with thin evidence.**  The phenomenon class is known; the specific two-learner
   instance, the receiver-relative contract and T1/T3 are candidates.  Before any scale-up: Q7b's replication gate, then a
   benchmark tier (RESCO / LibSignal with published controllers, IntersectionZoo fleets, ≥ 5 seeds).
3. **Cheapest experiments that the new neighbours make decisive** (proposed, not registered):
   (a) E3 + Decoupled-DC-style repair: replace stale relayed entries by a learned current-state estimate (no age relabel) — H1
       predicts it helps where relabelling hurt; a direct bridge to 2605.26286.
   (b) E3 + CALF / randomised-channel training as the published analogue of our mixture receiver — expected ≈ relayMIX; cite.
   (c) City: a VANET propagation search before C2 is used anywhere.

## Addendum 1 (00:37 EDT 03/10/2026) — external review 3 (user paste, "DECISION_FORKS_AND_HYPOTHESES_20261003"), verified
Verified first-hand:
* **RI Bayes decomposition (reviewer's G1) — REPRODUCED.** Their script (/Users/phanan/Documents/ChatGPT/CIG-AMF/research/
  catchup/ri_age_role_bayes_check_20261003.py, read in full, re-run from a scratchpad copy with OUT redirected) asserts the
  testbed sha in results.json = current scripts/RI_age_role_testbed.py, Schur check 2.7e-15.  Bayes MSE silent 1.389 (neural
  silent ≈ 1.39, consistent), trained window U{4..7} 0.619, upgrade window U{0..3} 0.223 at every λ (a rotation known to the
  Bayes predictor costs nothing).  Frozen receiver old → new: λ 0 0.622 → 0.249, 0.1 0.623 → 0.287, 0.2 0.625 → 0.601,
  0.4 0.634 → 2.982 (5 seeds); excess-risk change +0.023 / +0.060 / +0.372 / +2.744.  Limits as they state (expected Bayes
  risk, not sample-matched; linear-Gaussian RI only).
* **E3 analogue from existing data (no run): matched receiver as the information floor proxy.**  4×4 train-match report
  (e3_g4_train_match_report_20261002.txt, panel 4201–4264, 10 seeds, same panel): relayCK1 K1 +5.80, iid −3.55; relayCage iid
  +6.02, K1 −2.58.  Upgrade K1 → iid for the frozen CK1 receiver: −9.35 = information term +0.22 (Cage@iid − CK1@K1) + excess
  term −9.57 (CK1@iid − Cage@iid).  Downgrade for the frozen Cage receiver: −8.60 = −0.22 + −8.38.  3×3 (L-256 panel
  3801–3864): CK1 K1 +2.23, iid +0.17, relay6Cage iid +2.10 → information −0.13, excess −1.93 (seed sets differ: CK1 s0–4,
  6Cage s0–9 — recompute paired from rows.json before any use).  Reading: in E3 the K1 → iid change is nearly value-NEUTRAL
  for matched receivers; the whole hazard is receiver excess.  RI supplies the strictly-more-informative case (Bayes −0.40)
  where the hazard still appears.  Proxy caveat: a matched trained receiver is not the information-optimal policy.
* **Shisher–Sun (2208.06948v2) §III-B, Lemma 3 (eqs 25–26)** bounds the inference error's deviation by the χ² divergence β
  between training and inference CONDITIONAL laws.  So the distinction "they study the data process, we study training
  mismatch" (row above) is WRONG as stated; H1 (input edits must preserve the conditional law) is anticipated in theory and
  must cite Lemma 3.  Neither 2208.06948 nor the follow-up "Timely Communications for Remote Inference" (2404.16281) reports
  the stale-trained → fresh-deployed direction (WebFetch summaries of the HTML, not a full read).  E3's novel core stays: the
  upgrade direction for learned closed-loop decision receivers, the information-vs-excess split, support, rule A.
* **Proposal (a) above is withdrawn as stated.**  Decoupled DC (2605.26286) serves receivers trained on FRESH (synchronous)
  inputs; a current-state estimate would push our stale-trained receivers further out of support.  The analogue for our case is
  the opposite edit — GARBLING the upgraded channel back into the receiver's support (Blackwell emulation), which the RI
  testbed already ran (L-263: full emulation ≈ old performance, minimal emulation +0.63 > full +0.55 at every λ, AR3) but E3
  never did.  Candidate E3 test (not registered): receiver-side full emulation (throttle the iid deliveries to the K1 schedule)
  and minimal emulation (substitute the buffered value of the true older age for entries fresher than the trained range), eval-
  only on existing checkpoints; H1 predicts minimal/full ≫ remap.  Same object as Q7's cap (producer-side garbling).
* G6's tools are prior art: constrained BAI with feasibility tests (Cai & Kandasamy, 2511.09808) and policy testing in MDPs
  (Ariu et al., AISTATS 2026, PMLR 300) — any novelty must come from the value of receiver-in-the-loop measurements.
* G3 ≈ our H4; G4 ≈ H2b (Q7b B3); G5 ≈ H5 (B5) — already registered.  G7 (reconstruction vs task vs frozen-receiver floor) is a
  scope correction for LeanMarlReceiverFloor in the rewrite.  Check when Q7b lands (reviewer): exposure definition, ties,
  teleports / unfinished trips, cap chosen on seeds disjoint from the evaluation seeds.

## Addendum 2 (02:5x EDT 03/10, wake 1) — G1 / G3 recomputed from raw rows (subagent B, verified)
* **Correction to Addendum 1:** the 3×3 split "information −0.13, excess −1.93" compared CK1 s0–4 with 6Cage s0–9 (unpaired).
  Paired by seed: train-match panel 3201–3264 information **+0.83** [+0.25, +1.48] (5/5 > 0), excess **−2.94** [−4.10, −1.90]
  (I recomputed this panel independently: per seed +0.08 / +0.17 / +0.73 / +1.15 / +2.04, mean +0.83, excess −2.94); mixed panel
  3801–3864 +0.72 / −2.78.  4×4 unchanged (+0.22 [−0.25, +0.78] / −9.57 [−12.09, −7.16]).  Excess < 0 in 20/20 seed pairs in
  BOTH directions (downgrade 4×4 −8.37, 3×3 −4.30 / −4.09).  Excess carries 102 % (4×4) and 135–139 % (3×3) of the upgrade loss.
* **C0 exact split (regret units, c0_v3):** FT floor −3.27 vs excess +2.45 (5/5), EXT +1.21 / +20.93, CUT +0.86 / +0.70, A5
  +0.81 / +8.75; exact cost units FT −3.62 / +2.41 (excess eats 67 % of the information gain), EXT +5.71 / +21.78.
* **Proxy caveat:** against C0's exact floor, the matched-receiver proxy has Spearman 0.33 over 9 lights (bias +1.09; wrong sign
  on FT and A4) — the E3 "information term" is a matched-TRAINED receiver, not the information floor; say so in the paper.
* **G3 in C0:** Σ visitation × disadvantage over all cells IS the excess (performance-difference identity) — not a predictor.
  OOS-restricted disadvantage vs raw OOS mass: Spearman 0.873 vs 0.867 (33 cells); held-out lights A3–A6: 0.880 vs 0.831 but
  RMSE 2.18 vs 3.81; reverse 0.747 vs 0.746.  Ranking NOT better (the reviewer's kill rule for a transferable scalar
  certificate fires); magnitude ≈ 40 % better.  C0 cannot decide G3 further (OOS lights are nested extensions; in-support
  lights give both predictors 0).
* **Provenance:** scripts/CITY_c0_testbed.py reused `src` as a loop variable after storing the source sha (line 384), so c0_v3
  cells.json / result.json record "ACT"/"CUT" instead of a hash — demonstrated bug, fixed 02:56 (old file in legacy/); the v3
  panels were built 19:00–19:18 across a 19:13 edit, so the producing version is not verifiable from the record.  The 15 Z
  manifests of the 3×3 / 4×4 train-match panels record no checkpoint sha (mtimes predate the evaluations).

## Addendum 3 (07:5x EDT 03/10) — the upgrade-direction degradation HAS been observed (RDC, NeurIPS 2025) — E3's novelty narrows
Found by subagent A (benchmark survey), verified by me from the paper text (arXiv 2505.03586v4, WebFetch, verbatim sentence):
"The performance drop in the Base and Base+DR methods at delays of 0-2 reveals their inability to generalize to unseen delay
conditions during testing, despite successful convergence during training" (§ on Figs 8–9, fixed-delay tests on MPE).  So a
policy trained under delay (and one trained with delay randomisation over a range that excludes 0–2) losing when deployed
FRESHER is reported — as a side observation on generalisation, with RDC compensators as the remedy.  The numbers (e.g. "Base
≈ 125 at delay 6 vs ≈ 110 at 0" on TAG) come from a plot only (not in the text) and were NOT verified.
**Consequence for claim E3 (row above):** "the upgrade hazard, not found as such" is WITHDRAWN as a priority claim.  What
remains ours: (i) it is measured against a same-teacher compiled-silent bar — the upgrade makes communication worse than
silence; (ii) the information vs excess split (BCT update-gain form) with exact Bayes / C0 anchors; (iii) the support (joint
configuration) explanation — RDC's Base+DR failing at 0–2 is exactly an out-of-support randomisation range, i.e. consistent with
our account and a citeable confirmation; (iv) channel-side prospective prediction (rule A) and Lean knowledge floors; (v) which
repairs work (joint-level: matched / mixture training, FB_S fallback) and which do not (input relabel and per-entry / per-slot
garbling, L-295); (vi) decision-level flips on identical states (L-292).  The paper must cite RDC Figs 8–9 as the first
observation of the phenomenon in MARL.
