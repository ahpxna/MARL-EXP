# PROTOCOL — E3 paired repair panel (P1), 03/10/2026 18:1x EDT

Written before any run of the code it names (scripts/MARL_e3_repair_panel_eval.py and its RUN, QUEUE and report scripts).
Source of the requirements: PAPER1_DESTINATION_AND_CLOSURE_20261003 §4.4 and §5 P1, plus Addendum B items 1–6 (external
audit), and HANDOVER_AGENT_B_20261003 §5.  Status of the panel: **CONFIRMATORY** for the predictions in §6. The panel is not
used to design or tune P2. P2 uses development episodes 901–904 and a panel of its own.

## 1. Question

Several runtime repairs and retraining choices exist for a frozen relay receiver whose deployment channel differs from its
training channel. Under the same receiver checkpoint, the same seed blocks and the same channel randomness, what does each
one keep, block and cost?

The earlier evidence comes from four unpaired panels: 4901 (fallback), 5101 (emulation), 5201 (throttle / MASK) and 4601
(mixture). This panel replaces that patchwork with one paired table.

## 2. Panel

| Item | Value |
|---|---|
| Network | 4×4 CityFlow grid, relay v2 with the nearest8 slot restriction (scripts/MARL_grid_relay_wrapper.py) |
| Traffic seeds | **5301–5364** (checked unused: no script, protocol or result names it) × headways 8 / 16 = 128 episodes per cell |
| Actor seeds | 0–9; for each seed, every arm uses that seed's checkpoints |
| Deployment channels | K ∈ {1, iid, 2, 3}; iid is the exogenous capacity trace of `make()`, seeded by 5000 + 10·seed + load and independent of actions |

Pairing:

* Within an actor seed, all arms share the episode list, the capacity trace, the delivery rule (age-first prefix,
  MusicDelivery) and the CityFlow scenario files.
* No arm consumes extra randomness: CityFlow and the delivery rule are deterministic given actions, and the trace is
  exogenous.
* Arms differ only through their own actions. Different trajectories are therefore the treatment, not a pairing failure.

## 3. Receivers and arms

**Frozen receivers.** All runtime arms of one receiver share that checkpoint.

| Receiver | Trained on | Runtime arms |
|---|---|---|
| CK1 = relayCK1_st_s | const1 | PLAIN, MASK, FB_S+, FB_S−, FB_M+, FB_M−, FB_Mq+, FB_Mq−, EMU, THR |
| Cage = relayCage_st_s | iid | PLAIN, MASK, FB_S+, FB_S−, FB_M+, FB_M−, FB_Mq+, FB_Mq− |

EMU and THR are defined for upgrades only. Cage's training channel is the richest, so its throttle at k = ∞ and its emulation
floors reproduce PLAIN.

**Retraining arms.** These are different receivers and are reported apart from the runtime arms, with their training cost.

* **Matched receiver.**
  * Only two cells have one: CK1 at K = 1 and Cage at iid.
  * Cage is NOT called matched at K = 1, 2 or 3.
  * No 4×4 receiver was trained at K = 2 or K = 3, so those cells have no matched column.
* **MIX** = relayMIX_st_s: the four-regime mixture of test D. It runs PLAIN only.

**Silence bar.** Z = distill_none_s, the same-teacher compiled-silent student under delivery `none`, run once per episode.

**Arms.**

* **PLAIN.** The age-clip evaluator's path with A = −1, which equals RELAY of MARL_e3_fallback_eval_v2.
* **MASK.** The same receiver with every message removed (π^(−0), as in MARL_e3_joint_throttle_eval `masked`).
* **FB_\*.** The relay system in which an agent whose merged view is flagged acts with Z on the same view with messages removed
  (MARL_e3_fallback_eval_v2 `run_relay`). The relay protocol state is unchanged.
* **EMU.** Per-slot age emulation, the code of MARL_e3_age_emulation_eval mode `emu`, using the existing per-slot floors
  `e3_age_emulation_20261003/4x4/cal_relayCK1_st_s<s>/floors.json`. These are training channel K1, seeds 301–332, q = 0.05,
  sha-checked. The label is "per-slot emulation adapter (partial)". It is not an exact emulation.
* **THR.** Joint throttle at k_train = 1, the code of MARL_e3_joint_throttle_eval mode `thr`. It is an **input-only**
  intervention: `prev` and the sender-side mirror follow the unthrottled stream. The coordinated version is P2.

## 4. Detectors

All detectors read only the receiver's own merged view.

### 4.1 Shared distance and tie rule

This is the fix for §4.4 of the audit.

* One function: `d2(x, mu, P) = round(float(d @ (P @ d)), 9)` with `d = float64(x) − mu`. Calibration thresholds and runtime
  decisions both use it. No other path computes a distance; the old einsum-versus-matmul split is removed.
* Rounding to 9 decimals groups mathematically equal distances that float error separates.
* Every threshold is a value of `d2` on a calibration key, and a view is flagged iff `d2 > threshold`, strictly.
* The empirical threshold is the smallest calibration value v with weighted mass(d2 ≤ v) ≥ level, with ties grouped. The
  in-sample flagged mass is therefore ≤ 1 − level by construction.
* **No false-alarm guarantee is claimed.** Views within an episode are dependent; the leave-one-episode-out rate is reported
  as an estimate.

### 4.2 Calibration

* Calibration reruns the receiver's training channel on episodes 301–332 × {8, 16}, rotating regimes as in
  MARL_e3_fallback_eval_v2 `calibrate`, and keeps the counts per episode.
* **Parity.** The aggregate counts must equal the existing `e3_fallback_20261002/4x4/cal_<arm>_s<s>/calib.json` exactly.
  Otherwise the run stops.
* The detectors are built from those counts and frozen in `detectors.json`, with the sha of the calibration and of the
  checkpoint, before any panel episode.

### 4.3 The time bin is CONDITIONING, fixed here before any panel run

The key of FB_S is (time bin, 8 proportional age-count slots); the bins are t ≤ 4, 5–12 and ≥ 13.

* "+" detectors condition on the time bin: one support table, Gaussian and threshold per bin.
* "−" detectors pool the bins: the key without its time bin.
* Matched-feature comparisons are FB_S+ vs FB_M+ / FB_Mq+ and FB_S− vs FB_M− / FB_Mq−. Neither representation is chosen
  after the panel; both are reported.

### 4.4 The detectors

| Detector | Rule |
|---|---|
| FB_S± | Flag when the calibration count of the key is < 3. FB_S+ is the #3 FB_S rule. |
| FB_M± | Gaussian with weighted mean and covariance, pinv at rcond 1e-10, rank r. Flag when d2 > χ²_0.99(r). Full covariance with one prototype; this is a SIL-C-style parametric gate, NOT SIL-C's diagonal-prototype gate. |
| FB_Mq± | Same Gaussian, empirical 0.99 threshold under the §4.1 rule. This is the corrected FB_Mq. |

### 4.5 Recorded per detector

* In-sample false alarm.
* Leave-one-episode-out false alarm: refit without the episode, evaluate on it.
* Rank, threshold and number of keys.

**Change list.** For the old FB_Mq of v2: the calibration keys and weighted mass whose decision differs between the old gate
and FB_Mq−, per receiver.

## 5. Self-checks

The run refuses to write a manifest if any of these fails.

1. On the first episode of every cell:
   * a never-firing gate reproduces PLAIN exactly, and an always-firing gate reproduces Z exactly;
   * EMU with zero floors reproduces PLAIN;
   * THR with k = ∞ reproduces PLAIN.
2. The calibration-runtime parity of §4.2: the decisions recomputed from the loaded `detectors.json` equal the stored
   decisions on every calibration key.
3. Access invariants and the oracle guard at every step, and source hashes unchanged.
4. The smoke (before launch, traffic seeds 9001–9002, not evidence) also reproduces stored rows where available:
   * PLAIN and FB_S+ on panel 4901 (episodes seed4901–4902) against e3_fallback_mahal_20261003/4x4;
   * EMU on 5101 against e3_age_emulation_20261003/4x4;
   * THR and MASK on 5201 against e3_joint_throttle_20261003/4x4.

   All are compared at 1e-6. Smoke runs live under smoke/ and are not panel evidence.

## 6. Endpoints and predictions

These are fixed now. The cell groups come from the earlier panels 4201 / 4601 / 4901, not from this panel's signs.

**Cell groups.**

| Group | Cells |
|---|---|
| Own | CK1@K1, Cage@iid |
| Hazard | CK1@iid, Cage@K1 (negative mean on 4201, 4601 and 4901) |
| Benefit at risk | CK1@K2, CK1@K3, Cage@K2, Cage@K3 (positive mean on 4201 and 4901) |

**Statistics.**

* Gain vs Z: −(Σ waiting / Σ waiting of Z − 1) · 100 per actor seed.
* Mean over seeds, with a two-level bootstrap 95 % CI (2000 resamples, actor seeds and traffic seeds, rng 0, as in the
  earlier reports).
* Paired differences between arms are computed per seed.
* Per arm, also reported:
  * the intervention rate (fallback rate / substitution rate / drop rate);
  * the harmful-cell count (cells with CI upper < 0 out of 4);
  * the seed-level harmful share (gain < 0 among 40 seed × K units);
  * the worst-cell mean;
  * descriptive ratios: harm blocked = (arm − PLAIN)/(−PLAIN) in hazard cells, and benefit retained = arm / PLAIN in own and
    benefit cells. A ratio whose denominator CI contains 0 is marked unstable. These ratios are descriptive and never replace
    the paired gain.

**Predictions.** Each is SUPPORTED or NOT, with no post hoc rescue.

| ID | Prediction |
|---|---|
| RP1 (silence bar) | MASK has CI upper < 0 vs Z in all 4 cells, for both CK1 and Cage. |
| RP2 (hazard replication) | CK1 PLAIN at iid has CI upper < 0, and CK1 PLAIN(iid) − PLAIN(K1) has CI upper < 0. Cage PLAIN at K1 has CI upper < 0. |
| RP3 (support fallback blocks harm) | FB_S+ − PLAIN has CI lower > 0 in both hazard cells. |
| RP4 (no detector dominates) | For the matched pairs (FB_S+, FB_Mq+) and (FB_S−, FB_Mq−), neither member's mean gain is ≥ the other's in all 6 non-own cells (hazard + benefit). |
| RP5 (conservative support gate) | FB_S+ mean gain < PLAIN mean gain in ≥ 3 of the 4 benefit-at-risk cells. |
| RP6 (own-channel cost) | Every FB arm keeps ≥ 90 % of PLAIN's mean gain in both own cells. |
| RP7 (input-only repairs) | Neither EMU nor THR recovers ≥ 50 % of CK1's hazard at iid, i.e. arm(iid) − PLAIN(iid) < 0.5 · (PLAIN(K1) − PLAIN(iid)) on means. |
| RP8 (retraining vs runtime) | The matched receiver beats the best runtime arm of the mismatched receiver in that cell: Cage PLAIN@iid > max over CK1 arms@iid, and CK1 PLAIN@K1 > max over Cage arms@K1, paired per seed with CI lower > 0. MIX's worst cell > every runtime arm's worst cell, for both frozen receivers, on means. |

**Exploratory (no prediction).**

* The time-bin effect (+ vs −) per family.
* FB_M± vs FB_Mq±.
* The seed-level harmful shares.

## 7. Costs reported

| Cost | Source |
|---|---|
| Compute | Wall seconds per episode per arm; forward passes per decision: 1 relay, plus 1 Z for FB, plus 0 for EMU / THR. |
| Memory | EMU buffer: max entries held. THR shadow cache: entries. Detector size: keys / Gaussian parameters. |
| Bytes | Delivered direct packets × 25 B (relay v2 layout) per episode, identical across runtime arms on one channel. THR also records the packets it accepts. MASK and Z use 0 bytes, though the channel still transmits under MASK. |
| Retraining | From the checkpoints' training manifests and logs: iterations and wall time for CK1, Cage and MIX. The runtime arms cost 0 training plus one calibration pass (64 episodes). |

## 8. Legacy and reruns

* No earlier result is overwritten.
* Old FB_Mq rows stay in place and are marked superseded by the corrected FB_Mq in the report.
* After the main panel, the corrected FB_Mq− and FB_Mq+ are rerun on **every** cell of 4901 (4×4, both receivers, 10 seeds)
  and 4801 (3×3, 5 seeds) — all cells, not only the unfavourable ones. Each rerun gives a before / after table on the same
  panel.

## 9. Smoke result and freeze (18:19 EDT, before the panel launch)

The smoke was run on 03/10 from 18:12 to 18:19. It is NOT evidence. Smoke outputs are kept under
e3_repair_panel_20261003/smoke and smoke_pipe.

**Calibration parity.** For CK1 s0 and Cage s0, the counts summed over episodes equal the #3 calib.json exactly.

**Change list for the old FB_Mq.** For CK1 s0, one calibration key sat at the threshold. The old gate flagged it because of
the einsum-versus-matmul float difference, which put the old in-sample false alarm at 0.0385. FB_Mq− has 0.0000 on that key.
For Cage s0 nothing changed. FB_M− reproduces the old FB_M in-sample rate exactly (0.1538).

**Stored-row parity, at 1e-6, on 32 stored rows from 3 earlier panels:**

| Panel | Arms reproduced | Rows |
|---|---|---|
| 4901 | PLAIN, FB_S+, FB_M− | 12 |
| 5101 | PLAIN, EMU | 8 |
| 5201 | PLAIN, THR, MASK | 12 |

All first-episode identities passed: never- and always-firing gates, EMU with zero floors, THR at k = ∞.

**Smoke pipeline.** SMOKE=1 ran the queue, both reports and the rerun parity of PLAIN against the stored RELAY rows. The report
fixes made before launch were JSON serialisation of numpy integers, stored-row superset loading, and the channel bytes shown
for MASK. None of them changes a statistic or a verdict rule.

**Frozen for the panel** (sha256, first 16 hex):

| File | sha256 (first 16) |
|---|---|
| MARL_e3_repair_panel_eval.py | db7ceb9284d42999 |
| RUN_marl_e3_repair_panel.sh | b861411a79af1538 |
| QUEUE_marl_e3_repair_panel_20261003.sh | e15aa32a6d8a625e |
| MARL_e3_repair_panel_report.py | e3ad0397183830d6 |
| MARL_e3_fallback_eval_v2.py (imported) | 028890d5abd2f7b7 |
| MARL_e3_age_emulation_eval.py (imported) | fcec2a6daca28620 |
| MARL_e3_joint_throttle_eval.py (imported) | 23da6a3ced666ca4 |

**Inputs.**

* Checkpoints: e3_grid4x4_20260930/actors/{relayCK1_st, relayCage_st, relayMIX_st, distill_none}_s0–9; their sha is
  recorded per run.
* Floors: e3_age_emulation_20261003/4x4/cal_relayCK1_st_s*/floors.json (sha-checked against the checkpoint).
* Calibration: episodes 301–332 × 8/16.
* Panel: 5301–5364 × 8/16 (re-checked unused at 18:19).
* Lanes: 7, at nice 10.
