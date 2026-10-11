# PROTOCOL — P2: does the deployed upgrade NEST the old channel? (03/10/2026 18:3x EDT)

This protocol was written before any closed-loop run of PLAIN on the order-preserving channel and before any panel episode.

**Sources.**

* External audit PAPER1_DESTINATION_AND_CLOSURE_20261003, §5 P2 and Addendum C (two gates before the closed loop).
* Hypothesis from the handovers: input-only adapters fail because the protocol history is inconsistent.

**Status.** Confirmatory for N1–N5 below, on the new panel 5401–5464, which was checked unused at 18:33. Panel 5301 (P1) is
not read.

## 1. What was found before this protocol (gates)

All of the following used development episodes 901–904 and training episodes 301–332 only, with no closed-loop outcomes of
the arms below.

**Channel structure** (read from code: models/marl_delivery_music.py, envs/external/cityflow_hetero.py):

* There is one broadcast stream with a global order.
* Receiver i decodes the first K_i(t) senders of that order, excluding itself.
* The age-first order ranks senders by their last broadcast.
* Under K1, two senders are broadcast per step.
* Under the iid trace, K_i(t) is uniform on 1..m−2, so the broadcast set holds 14.7 of 16 senders per step on 4×4.
* **The order therefore depends on the capacity history.** A capacity upgrade changes the schedule itself.

**Gate 2, trace level** (scripts/MARL_e3_p2_replay_feasibility.py; schedules depend on the exogenous trace only; the trace
equals env._trace).

On the deployed iid upgrade (U1):

| Grid | K1 packets absent from receiver i's decoded prefix | Of which never broadcast | First miss | Position-1 agreement with K1 |
|---|---|---|---|---|
| 4×4 | 50.8 % of (i, t) | 13.2 % | step 1 in every episode | 4.9 % |
| 3×3 | 55.5 % | 24.5 % | step 1 | 18 % |

Entry-level availability of the K1 merged view to a receiver-only emulator, counting direct decodes plus the tables carried
in decoded packets (slot-restricted):

| Grid | U1 (iid, adaptive) | Constant K2 (adaptive) | U2 (order-preserving) |
|---|---|---|---|
| 4×4 | 79 % (direct 50 %) | 7 % | **100 %** |
| 3×3 | 75 % | 25 % | **100 %** |

The function can fail: self-pairs give 100 % and downgrades give 6–11 %.

**Gate 1, information.**

* The order-preserving scheduler (U2) uses only scheduler records: it ranks with the K1 rule on a legacy history and fills the
  extra capacity with the later positions of that order.
* The receiver-side exact emulator (EXACT) uses only the receiver's own decoded packets and the tables those packets carry,
  plus the public legacy schedule, which is a deterministic function of time.
* There is no ACK and no read of another node's state.

**Gate 2, closed-loop replay** (scripts/MARL_e3_p2_nesting_replay.py, dev episode 901, receiver CK1 s0).

* With every agent running EXACT on U2, the run is identical to the K1 run at every step: packet sets, view entries
  (sender, measured_at, age, payload), encoded inputs, actions and queue (3×3 1830 = 1830; 4×4 1574 = 1574; 0 entries
  missing).
* Negative control: EXACT on U1 locked to K1 FAILS at t = 1.
* On U1 the emulator misses 18.6–25.2 % of K1 entries (4×4, 8 dev episodes).

**Reading.** On the deployed upgrade, no receiver-side adapter can reproduce the training channel. The old channel is not a
garbling of the new one at the receiver, because the scheduler re-orders. An order-preserving upgrade nests it, and an exact
receiver-side emulator exists.

All agents running EXACT recover the K1 trajectory. This is a **positive control / rollback at the receiver**, not a method
that uses the extra capacity (audit Addendum C).

## 2. Panel

| Item | Value |
|---|---|
| Network | 4×4, relay v2 nearest8 |
| Traffic seeds | 5401–5464 × {8, 16} |
| Actor seeds | 0–9 |
| Z | distill_none_s, run once per episode |

**Channels:**

* **K1:** const1, age-first. The CK1 receiver's training channel.
* **U1:** the iid trace, age-first. This is the deployed upgrade, where the hazard is.
* **U2:** the same iid trace with NestedDelivery: the legacy K1 order with extra capacity in its later positions.

**Arms.** The team is homogeneous: every agent runs the arm.

| Receiver | Arms |
|---|---|
| CK1 | K1/PLAIN, U1/PLAIN, U2/PLAIN, U2/EXACT, U1/EXACT |
| Cage (trained on U1) | K1/PLAIN, U1/PLAIN, U2/PLAIN |
| MIX | K1/PLAIN, U1/PLAIN, U2/PLAIN |

**U1/EXACT on missing entries.** It shows the most recent seen copy of j measured before m*, with its true age. If there is
none, the entry is absent. The rule is fixed here and counted per episode.

**In-run self-checks.** The run refuses to write a manifest if any of these fails.

* U2/EXACT is locked step by step to K1/PLAIN on EVERY episode: packet sets, view entries, encoded inputs, actions and queue
  must match exactly.
* U2 nests K1 at every step.
* Access invariants, the oracle guard and source hashes hold.

## 3. Predictions

Endpoints: gain vs Z per seed, a two-level crossed bootstrap 95 % CI (2000 draws, rng 0), and paired differences per seed.

| ID | Prediction |
|---|---|
| **N1 (replay, implementation)** | CK1 U2/EXACT equals CK1 K1/PLAIN on every episode, asserted in-run. |
| **N2 (non-nesting, quantified)** | The U1/EXACT missing-entry share is ≥ 10 % on every seed. |
| **N3 (receiver-side repair on the deployed upgrade is partial)** | (a) CK1 U1/EXACT − U1/PLAIN > 0 with CI lower > 0; (b) CK1 U1/EXACT − K1/PLAIN < 0 with CI upper < 0. |
| **N4 (a nested upgrade still hurts the frozen receiver)** | CK1 U2/PLAIN − K1/PLAIN < 0 with CI upper < 0. |
| **N5 (nesting has a cost for receivers trained on the adaptive channel)** | Cage U2/PLAIN − U1/PLAIN < 0 with CI upper < 0. |

How N4 is read:

* If N4 holds, then even when the new channel contains the old one, the frozen receiver cannot use the extra packets, and the
  hazard is about USE, not missing information. The exact emulator then restores K1 performance at zero retraining cost
  (N1).
* If N4 fails, the hazard on U1 comes from the scheduler's re-ordering, not from the extra information.

Exploratory:

* MIX on U2;
* bytes delivered under U1 vs U2;
* the emulator's buffer memory;
* the size of the hazard on U2 vs U1.

## 4. Costs

* Delivered direct packets × 25 B per episode for each channel.
* The EXACT buffer: the number of (sender, measurement time) copies held.
* Runtime per episode.
* No retraining.

## 5. What this can and cannot show

**Can:** the channel property that decides whether a receiver-side repair exists (nesting), verified by exact replay, and
whether the nested upgrade is harmful to the frozen receiver.

**Cannot:**

* a method that exploits the upgrade for the frozen receiver (EXACT discards the extra packets);
* the general MARL claim;
* anything about other schedulers.

The Lean `emulation_repairs` is a sufficient condition. Exact replay on U2 is an implementation check on these traces, not a
proof of equality of laws for every history.

## 6. Smoke and freeze (18:36 EDT, before the panel launch)
Smoke (traffic 9001-9002, seed 0; NOT evidence): pipeline through the report; U2/EXACT locked to K1/PLAIN on both episodes (identical); U1 missing share 0.216.  Frozen (sha256, first 16 hex):
* MARL_e3_p2_nesting_eval.py fbe20414e3bef68c
* MARL_e3_p2_nesting_replay.py 75680231d82340a2
* RUN_marl_e3_p2_nesting.sh 761c3ecf903214b6
* QUEUE_marl_e3_p2_nesting_20261003.sh 6711ea20bbadbcc2
* MARL_e3_p2_nesting_report.py 5f343b84aee00d19
* MARL_e3_p2_replay_feasibility.py 785ae7ff62908746
Lanes 3 (nice 10), concurrent with the P1 queue (7 lanes).

## 7. Amendment 1 (19:14 EDT, after the first panel run aborted; predictions, endpoints and thresholds UNCHANGED)
* What happened: the in-run lock aborted every CK1 job at traffic seed 5407 load 16, t = 23, receiver 4. The K1 view holds sender 15's copy measured at 150; receiver 4 never received that copy on U2, so EXACT showed the 140 copy. That is 1 missing relayed entry of 3508 in the episode.
* Re-measured on traces only, with no closed-loop outcome, over 136 non-panel episodes (301–364 and 901–904, × 8/16):
  * U2 availability on 4×4 = 0.999992 on average, minimum 0.99943, with 3 episodes having a miss: 303/16, 311/8, 338/8.
  * U2 availability on 3×3 = 1.0 in all 136.
* Correction: the gate's "100 %" was measured on 8 dev episodes and is an overclaim. U2 always contains the K1 DIRECT packets. On 4×4, slot-restricted relay can miss rare relayed copies.
* **N1 is therefore NOT SUPPORTED as registered** (exact on every episode). It is reported with counts.
* Change: the U2/EXACT lock RECORDS, per episode, the number of mismatched steps, the first mismatch and queue equality, instead of aborting (scripts/MARL_e3_p2_nesting_eval.py --record-lock, used for CK1 only). Everything else is identical. The Z, Cage and MIX jobs of the first run are complete under the frozen code and are kept.
* Smoke of the new path (training traces 303 and 311; not evidence): 1 mismatched step in 311/8 (t = 17) and in 303/16 (t = 23); queue equal to K1 in both.
* **Disclosure.** Before this amendment, the aborted CK1 logs had already printed per-episode queue sums for traffic seeds 5401–5406, for all CK1 arms on seeds 0–9. These were seen while diagnosing. No prediction, endpoint, threshold or comparison was changed after seeing them.
Frozen after Amendment 1 (sha256, first 16 hex):
* MARL_e3_p2_nesting_eval.py d4d1c0171f4d2d26
* MARL_e3_p2_nesting_replay.py ff4e88922b0be3f7
* RUN_marl_e3_p2_nesting.sh 4c959549da9e06ff
* MARL_e3_p2_nesting_report.py d10c2838c8a48ad0

## 8. Amendment 2 (20:0x EDT, 03/10; external audit ADAPT_V12_P2_AUDIT + P2_COMPLETED_EVIDENCE_AUDIT; reporter only, no rerun)

**Reporter fixes** (scripts/MARL_e3_p2_nesting_report.py; the earlier report is archived in legacy/p2_report_before_amendment2_*):

* N1 now also requires every U2/EXACT episode to have `lock_mismatch_steps == 0` and an equal queue. The old rule used only
  queue equality plus "locked", so a one-step replay mismatch could have passed. The verdict is unchanged: NOT SUPPORTED.
* A missing registered seed gives INCOMPLETE and no verdict.
* New exploratory line:
  * CK1 U2/PLAIN − U1/PLAIN = +1.05 [−0.21, +2.52] (6/10 > 0). This is an estimate, NOT a bound or a causal split.
  * U2/EXACT − K1/PLAIN = −0.0032 [−0.0104, +0.0002].

**Runner fix.** RUN_marl_e3_p2_nesting.sh now propagates exit codes instead of `|| echo FAIL`.

**Wording corrections to L-305 / L-308**, as required by the audit:

| Do not say | Say instead |
|---|---|
| "re-ordering accounts for at most ≈ 1 point" | U2 − U1 = +1.05 [−0.21, +2.52] is an estimate, not an upper bound or a decomposition. |
| U2 "contains" the old channel, "exact emulator" | U2 keeps the K1 DIRECT packets. On 4×4 it misses rare relayed copies (N1 NOT SUPPORTED). Call EXACT a near-exact emulator. |
| "equal to K1", "removes the hazard entirely" | −0.0032 [−0.0104, +0.0002]: very close to K1, not identical; 8 episodes have a different queue. |
| "partial emulation hurts BECAUSE of joint inconsistency" | This partial emulator hurts (−4.17 [−8.34, −0.14]). The cause is not separated from dropping new information, using older copies, or the age / mask change. |
| "mixed-version fleets: beats fallback and network rollback" | NOT TESTED. P2 has homogeneous teams only; mixed policies change the whole team's actions and traffic. A mixed-team panel is needed (see PROTOCOL_E3_MIXED_FLEET_20261003). |
| N5 failing = "no cost" | Non-inferiority is not established: Cage's CI reaches −0.64, beyond a 0.5 margin. |

**Cost.** U1 and U2 deliver about 7.5× the bytes of K1 (77 962 vs 10 400 B per episode). "No retraining" does not mean
"no cost".

**Headline (the audit's wording).** On the same U2 channel and the same CK1 checkpoint, changing only how the input is built
(the near-exact emulator) raises the gain by +8.13 points [+5.67, +10.54] without retraining.
