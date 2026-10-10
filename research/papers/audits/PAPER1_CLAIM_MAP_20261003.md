# Paper 1 — claim map (P0), 03/10/2026 18:2x EDT

Source of the task: PAPER1_DESTINATION_AND_CLOSURE_20261003 §5 P0 and Addendum A–F (external audit), and HANDOVER_AGENT_A / B.
No simulation was run for this map.

**Provenance.** Scanned by `scripts/PAPER1_claim_provenance.py`, output in
`research/papers/audits/paper1_claim_map_20261003/provenance.{json,txt}`. On every panel listed, each producer hash recorded
in the run manifests equals the current file. Checkpoint sha equals the current checkpoint wherever one was recorded. The
gaps are in §5.

**Comparator** throughout: the same-seed compiled-silent student Z (distill_none_s, delivery `none`).

**Gain vs Z** = −(Σ waiting / Σ waiting of Z − 1) · 100 per actor seed, so positive means better than Z.

## 0. Message of the paper (what the claims serve)

An evaluation of **deploying a frozen learned receiver after the communication channel changes**:

1. **Useful information and a receiver that can use it are different things.** An upgraded channel can carry more
   information while the frozen receiver does worse. This is exact in the RI testbed; on traffic only a matched-training
   contrast is available.
2. **When the receiver can be kept, when a fallback is enough, and when it must be retrained**, measured under the same
   conditions and with costs (P1, panel 5301).
3. **One concrete cause** (P2; gates passed, panel 5401 pending):
   * **Mechanism.** The deployed capacity upgrade does not nest the old channel, because the adaptive scheduler re-orders.
     So no receiver-side adapter can reproduce the training input; 50.8 % of K1 packets are absent.
   * **Exact repair under nesting.** When the upgrade nests the old channel, an exact receiver-side emulator exists and
     replays K1 exactly. Whether the nested upgrade still hurts the frozen receiver is N4.

RDC (NeurIPS 2025) already shows a drop in the upgrade direction. We do not claim to be first to observe it.

## 1. Empirical claims

Every claim has ONE primary panel. Numbers come from the stored report of that panel unless marked "recomputed" (computed
here, 18:2x).

| ID | Claim (scoped wording) | Primary panel / raw rows | Seeds | Comparator, statistic [95 % CI] | Secondary / notes |
|---|---|---|---|---|---|
| E1 | On its own training channel, the relay receiver beats the silent student Z on 4×4. | 4201 `e3_g4_train_match_20261002/R_*`, `Z_s*`. Producer `MARL_e3_ageclip_eval.py` (A = −1). Relay sha recorded = current. | actors 0–9; traffic 4201–4264 × 8/16 | vs Z: Cage@iid +6.02 [5.01, 7.21]; CK1@K1 +5.80 [4.38, 7.15]; 10/10 seeds > 0 for both | 3×3: 3801 relay6Cage@iid +2.10 [1.19, 3.05]. The reserved panel 2701 lacks relay sha (§5). |
| E2 | **Upgrade direction.** The K1-trained receiver deployed at iid loses its K1 gain on both grids. On 4×4 it falls below Z; on 3×3 it ends near Z, not below. | 4201 (as E1) | as E1 | CK1@iid −3.55 [−6.22, −0.94]. Paired iid − K1: −9.35 [−12.15, −6.58], 0/10 > 0 (recomputed). | 3×3 3201: iid +0.29 [−1.62, 2.07] vs K1 +2.40 [1.36, 3.42]. Replications: 4601, 4901, 5101, 5201 (same checkpoints, NOT independent). |
| E3 | **Downgrade direction.** The iid-trained receiver at K1 falls below Z. | 4201 | as E1 | Cage@K1 −2.58 [−3.97, −1.32]; paired K1 − iid −8.60 [−10.29, −6.77] (recomputed) | 3×3 3201: −1.90 [−3.67, −0.21]. 3301 G1 (same checkpoints). |
| E4 | Matching the training channel to the deployment channel helps at the **two channels where a matched receiver exists**. | 4201 | as E1 | CK1 − Cage @K1 +8.11 [6.04, 9.97], 10/10 (report); Cage − CK1 @iid +9.57 [7.06, 12.24], 10/10 (recomputed) | 3×3 3201: +4.18 [2.04, 6.15] @K1; −3.03 [−4.27, −1.91] @iid. No 4×4 receiver trained at K2 / K3. |
| E5 | A receiver trained on a four-regime mixture has the best worst cell among the 4×4 receivers tested. It pays a premium of about 0.5 point on each specialist's own channel. | 4601 `e3_g4_mix_20261002`; relay sha = current; Z sha not recorded | actors 0–9; traffic 4601–4664 | MIX vs Z: K1 +5.27 [3.91, 6.59], K2 +5.78, K3 +5.98, iid +5.83. D1, D3 SUPPORTED; **D2 NOT** (−0.52 vs Cage at iid). | 3×3 3801: MX1 +0.97 [0.34, 1.64]; MX3 NOT (−1.05 vs CK1 at K1). **Do not write "minimax".** |
| E6a | **Information vs use, exact (RI).** The Bayes risk falls with the upgrade while the frozen receiver's risk can rise, through its excess alone. | `ri_age_role_20261002/results.json`, producer `RI_age_role_testbed.py` (sha = recorded) | 5 seeds × 4 drifts | Bayes MSE 0.619 → 0.223. Frozen receiver's excess change +0.023 / +0.060 / +0.372 / +2.744 (λ = 0 / 0.1 / 0.2 / 0.4) | Linear-Gaussian testbed. This is expected Bayes risk, not sample-matched. |
| E6b | **Information vs use, traffic (proxy).** A matched-training reference contrast, NOT a Bayes decomposition. | 4201 (relay rows), G1 by subagent B | actors 0–9 | Upgrade K1 → iid split into reference +0.22 [−0.25, 0.78] and residual −9.57 [−12.09, −7.16]; residual < 0 in 20/20 seed pairs | Do NOT write "excess risk" or "no information loss" for E3. C0 is secondary (producer unverifiable, C-9). Against C0's exact floor the proxy has Spearman 0.33. |
| E7 | Descriptive support diagnostics: which statistic leaves the training support. | 3×3 L-268; 4×4 L-271 / L-272 | — | descriptive | Post hoc. Not a causal claim. |
| E8 | A channel-side rule (rule A, training-relative threshold) classified the sign of 3 of 3 4×4 constant-K cells before the run. | 3301 + Addendum 4 | 3 cells | 3/3 (absolute version 1/3) | n = 3 cells: an anecdote, not a validated predictor. |
| E9 | Detectors on the receiver's own view (support count, Gaussian distance) **trade blocking harm against keeping benefit**. Neither dominates. | **5301 (P1, pending).** Old evidence: 4901 per-cell table (handover B §3) | — | Per cell: paired gain, fallback rate | The 99.8 % / 72 % harm blocked and < 0 % / 44 % benefit kept were retrospective, computed on the 4 non-own cells with positive mean only, with no CI: **descriptive, scope stated**. Do not write "FB_S drops all communication benefit". |
| E10 | Teacher-relative disagreement: on Z-driven states, the frozen receiver's agreement with the teacher's A_0.25 acceptable set falls after the upgrade. | dev 901–904 `e3_crosschannel_flip_20261003` | 4×4 actors 0–9 | CK1 const1 → iid net −0.084, 10/10 < 0 | Diagnostic: teacher-relative, NOT "wrong actions". One direction per pair only (NF(A→B) = PF(B→A)). |
| E11 | The masked-message reference π^(−0) of CGDC-style analyses is far weaker than Z. Against a masked reference every hazard would look like a gain. | **5301 (RP1).** Old evidence: 5201 | — | 5201: CK1 MASK −14.87 [−26.83, −7.02]; Cage −15.30 [−19.97, −10.46] | 3×3 −4.07 / −4.55. |
| E12 | Input-only interventions at the receiver (per-slot emulation adapter, input-only joint throttle) do not repair the upgrade hazard. | **5301 (RP7).** Old evidence: 5101 (EMU), 5201 (THR) | — | 5101: EMU − PLAIN +0.75 [−1.01, 2.32]; EMU − LAB +4.63 [2.83, 6.32]. 5201: THR − PLAIN −11.15 [−14.13, −7.84]. | THR is input-only (`prev = mv`, the mirror is unthrottled). EMU is partial: 1 108 050 of 3 612 970 below-floor entries had no older copy. |
| E13 | **Deployment table**: gain, paired Δ, fallback rate, harmful cells, costs (runtime vs retraining). | **5301**, PROTOCOL_E3_REPAIR_PANEL_20261003 | actors 0–9; traffic 5301–5364 | RP1–RP8 | pending |
| E14 | Second domain (SUMO, city track): a learned light can regress an old learned fleet; a producer-side compatible mode (max-green cap 50 s) keeps most of the gain. | C-8 | 4 training seeds | B1 NOT (3 of 4 pairs); B2 SUPPORTED | Secondary. G5: low power (C-10). |

## 2. Theory claims

Wording follows handover A §5. Every theorem is stated under **fixed input distributions, open loop**.

| Claim | Module / theorem | Scope | Gate | Empirical link (only "consistent with") |
|---|---|---|---|---|
| Knowledge floor: no scheduler lets a receiver know more than Σ_{s<n} K*(s) recent measurements | ReceiverFloorV2.receiver_floor, PrefixInstanceV1, ReceiverFloorV1.timed_forced_stale | full-relay knowledge model; knowledge, not decisions | smoke | stale tail at constant K |
| Channel cap behind rule A | ProvisioningV1.provisioning, NetFloorV1.net_floor | constant K; cap only, no sign | smoke | E8 |
| A training-optimal frozen receiver can be worse than silence on a Blackwell-dominating channel | SupportV1.upgrade_hazard; FrozenFloorV1.frozen_floor_not_monotone | one finite example | SupportV1 smoke; FrozenFloor compiled only | E2 |
| Sufficient condition for emulation (hpush, hsem) | FrozenFloorV1.emulation_repairs | sufficient only; hpush NOT shown for any E3 garbling | compiled only | target of P2 |
| Marginal matching is not enough | FrozenFloorV1.marginal_match_insufficient | one example | compiled only | E12 (EMU) |
| No certificate from the two channel laws alone | CityReceiverContractV1.no_receiver_free_certificate | one example | compiled only | motivates receiver-relative detectors (E9) |
| Deciding can need fewer decoded senders than identifying | TaskVsReconV1.task_lt_reconstruction | static, m = 3 | compiled only | scope note |

**Before citing:** smoke-gate FrozenFloorV1, TaskVsReconV1 and CityReceiverContractV1 (P4).

**Not in Lean:** the RI decomposition (a computation), the dynamic task floor, any closed-loop or return bound, hpush in E3.

## 3. Pooling, independence and CI rule

* **Primary panels are used once** and quoted with their own CI.
* **Replications reuse checkpoints.** Panels 4601, 4901, 5101, 5201 and 5301 re-evaluate the same 10 4×4 checkpoints per
  receiver type, and the 3×3 panels re-evaluate 5–10 checkpoints. They are NOT independent replications of the training
  randomness, and are counted as "re-evaluated on new traffic seeds".
* **Train × deploy matrix ("diagonal best 30/30").** Descriptive only. The pooled cells mix seed sets and panels; K1 and iid
  pool more panels than K2 and K3; the 4×4 cells include test D. F1 must show one primary panel per receiver set (4201 + 4601
  for MIX) and give the pooling rule in the caption.
* **CI method: one rule for the paper** (found while building this map):
  * Two different two-level bootstraps are in use. 4201 and 4601 use 4000 draws, with an independent traffic resample per
    drawn seed. 5101, 5201 and the repair panel use 2000 draws, with ONE traffic resample per draw shared by all drawn seeds.
  * The shared resample matches the crossed design: every actor seed meets the same traffic seeds.
  * It is fixed as the paper's CI. In P5 every main-table and figure CI is recomputed with one function. Differences seen
    here are ≤ 0.1 point; for example, CK1@K1 4201 is [4.38, 7.15] in the report and [4.31, 7.09] with the shared rule.

## 4. Wording rules

| Drop | Use instead |
|---|---|
| "minimax receiver" | "mixture-trained receiver; best worst cell among the receivers tested (4×4)"; also D2 NOT SUPPORTED at iid (−0.52) |
| "iff" (emulation) | "sufficient condition (hpush, hsem); not necessary; hpush not shown for E3" |
| "exact E3 (Bayes) decomposition", "the loss is excess risk, not lost information" (E3) | RI: exact. E3: "matched-training reference contrast" |
| "proven safe action flips", "wrong actions" | "disagreement with the teacher's A_0.25 set on Z-driven states" |
| "receiver-only repair impossible" | "the receiver-side input interventions we tested did not repair it" |
| "FB_S beats the standard gate" | "trade-off: FB_S blocks more harm, the Gaussian quantile gate keeps more benefit; neither dominates (per cell)" |
| "FB_S drops all communication benefit" | per cell: own channel retained; the benefit-at-risk cells give it up |
| "Base+DR = delay randomisation"; "142.3 is Base" | DR = delay-reconciled critic. TAG Base 110.2 / 135.2 / 125.4 at delays 0 / 3 / 6; 142.3 is Base+DR at 6 |
| "the support is co-produced" (as a result), "joint support is the cause" | hypothesis for P2 |
| "decision floor" | "knowledge floor" |
| "first to observe the upgrade hazard" | "RDC reports a drop in the upgrade direction; we measure it against Z and map repairs" |
| "an input-only throttle emulates the training protocol" | "input-only intervention; `prev` and the mirror follow the unthrottled stream" |
| "EMU = exact emulation" | "per-slot emulation adapter (partial)" |

## 5. Provenance gaps

* **Z checkpoints.** No Z manifest on any panel records the Z checkpoint sha. A checksum computed today does not repair the
  history; state this. The relay-side sha is complete on 3201, 3801, 4201, 4601, 4801/4901 and 5101/5201.
* **No relay sha** on 2701 (reserved 3×3 panel, L-201) or 2801 (frontier). These are secondary only.
* **C0** producer unverifiable (C-9). Secondary, with the caveat, unless rerun frozen.
* **Smoke and partial runs** are archived in legacy/ and never quoted.

## 6. Status of the paper's pillars

| Pillar | Status |
|---|---|
| Hazard in both directions vs Z | closed on 4201 (E2, E3); 3×3 scoped |
| Information vs use | RI closed (E6a); traffic = proxy (E6b) |
| Deployment table: keep / fallback / retrain, with costs | P1 running (E13) |
| Cause (P2) | panel 5401 done (L-307 … L-309).

* **Headline.** On the same U2 channel and the same CK1 checkpoint, changing only how the input is built (the near-exact emulator) gives +8.13 [+5.67, +10.54] with no retraining.
* **A nested upgrade still hurts:** U2 − K1 −8.13 (N4 SUPPORTED).
* **U2 − U1 = +1.05 [−0.21, +2.52]**, an estimate, not a bound.
* **Near-exact, not exact:** U2/EXACT − K1 = −0.0032 [−0.0104, +0.0002]; N1 NOT SUPPORTED.
* **The partial emulator on U1 hurts:** −4.17. The cause is not separated.
* **Nesting cost for Cage:** non-inferiority NOT shown (CI to −0.64).
* **Mixed-version fleet:** NOT TESTED.
* **Bytes:** U1 / U2 deliver 7.5× the K1 bytes. |
| External benchmark (P3) | needs download permission; replication of RDC kept apart from the MPE2 adaptation |
| Plain fine-tune baseline | not started; needed before any PCT-style penalty |
