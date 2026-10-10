# Where the project stands, what is proved, what is left, novelty and story — 03/10/2026 23:5x EDT

Sources: ledger L-01 … L-318, claim map, protocols of 03/10, the external audits of 03/10, today's results.

## 0. The current goal (as fixed by the user and the audits on 03/10)

A paper with a METHOD ADVANTAGE in a concrete deployment problem.

* **The problem.** A multi-agent system with learned communicating receivers gets a communication upgrade while some receivers
  cannot be retrained. That makes it a mixed-version fleet.
* **Primary candidate.** A compatibility layer, i.e. a legacy-order scheduler plus a receiver-side packet-only emulator, or
  legacy-state base packets.
* **Comparators:**
  * runtime fallbacks;
  * rollback;
  * fine-tuning (FT-mix / PCT / BCWI);
  * retraining.

  All are compared with costs.
* **Supporting results:** the deployment evaluation (hazard both ways vs a strict silence bar), information vs use, and the
  mechanism.
* **Venue fit:** TMLR-like.

## 1. Completion against that goal: ≈ 55 %

| Part | Weight | Done | Status |
|---|---|---|---|
| Evidence base: hazard both ways vs Z, primary panels, claim map, provenance (P0) | 15 | 90 % | Done. A single CI function for every figure is pending (P5). |
| Information vs use (RI exact; E3 proxy; G1 / G2) | 10 | 85 % | RI closed; E3 stays a proxy. |
| Runtime repair table (P1 + E8 stronger Gaussian) | 10 | 80 % | P1 closed; E8 running. |
| Mechanism (P2 + E6 + E9 + E3 cause test) | 15 | 75 % | N4, E6 and E9 partly closed; E3 running. |
| **Method: compatibility layer in mixed fleets (E7)** | 20 | 40 % | Pilot GO; confirmation running (about 01:30). |
| Learned adaptation (FT-mix / PCT / PAIRED; E11, E2, E10) | 10 | 50 % | Pilot NO-GO for PAIRED; E11 running; E2 / E10 queued. |
| External validity (NYC; independent benchmark P3) | 10 | 10 % | NYC blocked by RAM; P3 needs download permission. |
| Theory section + Lean gates for the cited modules | 5 | 55 % | Modules compiled; 3 not smoke-gated; nesting lemma not written. |
| Manuscript, figures, reproducibility package | 5 | 25 % | Draft v2 exists; F1–F5 to regenerate. |

## 2. What still has to RUN

* **Running now:**
  * E3 (missing-entry rule);
  * E11 (from scratch at 8–80 episodes);
  * E7 (mixed-fleet confirmation, 10 seeds, FT / PCT-old, FBR, EXACT_PROTO arms);
  * E8 (residual-guarded Gaussian);
  * E9 replay (64 / 64 exact so far).
* **Queued:** E2 (data factorial + UNI) and E10 (PAIRED v2).
* **Not started:**
  * NYC students: they need about 32–64 GB RAM, or a recorded protocol change.
  * P3 independent benchmark: needs your download permission.
  * G3: C0 frozen rerun, then weighted out-of-support mass.
  * G4: SUMO receiver stub.
  * G6: offline sequential "adequate upgrade" search on the Q7b rows.
  * The P5 figure / CI regeneration.
  * Comparison with published comm-MARL baselines.

## 3. What still has to be PROVED (Lean / math), for the claims the paper would make

1. **Nesting lemma** (new, needed for the method).
   * Statement: if under the new schedule every receiver's decoded history determines its legacy decoded history (prefix
     nesting plus legacy state in base packets), then the legacy merged view is a measurable function of the new observations.
     The exact emulator then exists (hpush holds), and `FrozenFloorV1.emulation_repairs` applies.
   * Empirical counterpart: E9 is exact 64 / 64. EMU without legacy state is near-exact (N1 failed on rare relayed copies,
     so it needs the legacy-state version).
2. **Non-nesting obstruction.** A small explicit instance in which age-first scheduling with a larger capacity re-orders
   broadcasts, so the legacy view is not a function of the new observations. Empirically, 50.8 % of direct K1 packets are
   absent on 4×4.
3. **Smoke gates** for FrozenFloorV1, TaskVsReconV1 and CityReceiverContractV1, before citing them.
4. **Not provable / not claimed:**
   * any closed-loop return bound;
   * mixed-fleet guarantees;
   * that support is the unique cause.

## 4. Hypotheses checked so far (selected; full list in the ledger)

| Hypothesis | Verdict | Evidence |
|---|---|---|
| A relay receiver clears the compiled-silent Z on its own channel | SUPPORTED | 4201: +5.80 / +6.02 |
| Upgrade hazard (K1-trained at iid) / downgrade hazard | SUPPORTED | 4201: −3.55 / −2.58; 5301 RP2 |
| Matched training rescues (K1, iid) | SUPPORTED | +8.11 / +9.57 |
| Mixture = minimax | NOT (premium; D2 failed) | 4601 |
| Masked reference is weaker than Z | SUPPORTED | RP1 |
| Support fallback blocks harm but gives up benefit; no detector dominates | SUPPORTED | RP3–RP5 |
| Input-only adapters (relabel, remap, clip on 4×4, per-slot EMU, throttle) repair the hazard | NOT | L-266, L-274, 5101, 5201, RP7 |
| Exact emulation on the deployed channel is possible | NOT (21.6 % of entries missing) | P2 N2 |
| A nested upgrade still hurts the frozen receiver (use, not missing information) | SUPPORTED | P2 N4: −8.13 |
| A near-exact emulator on the nested channel restores K1 without retraining | SUPPORTED as a measurement (+8.13; −0.0032 vs K1); exact replay N1 NOT | P2 |
| The emulator uses only packet-recoverable metadata | SUPPORTED | E6: 0 ambiguous |
| A legacy-state protocol is exact | SUPPORTED so far | E9: 64 / 64 |
| Mixed fleet: compatibility layer beats fallback / plain / rollback | Pilot GO (5 seeds) | L-313 |
| PAIRED adaptation beats FT-mix / PCT | NOT | adaptation pilot NO-GO |
| FT-mix closes most of the hazard in 80 episodes, old channel kept | Observed (2 seeds) | L-312 |
| RI: a Blackwell garbling ≈ actual emulation | SUPPORTED | G2b |
| RI: law-matching garbling beats plain | NOT | G2a |
| RI: the information-preserving transport beats garbling | Observed, against prediction | G2c |
| SUMO: the old fleet regresses under a learned light | 3 / 4 pairs (B1 NOT) | — |
| SUMO: max-green 50 s keeps most of the gain | SUPPORTED (B2) | — |
| SUMO: contracts rank harm | NOT (B3) | — |

## 5. Proved (compiled Lean, standard axioms, under their hypotheses)

| Theorem | Status |
|---|---|
| Knowledge floors: receiver_floor, net_floor, prefix / timed variants | smoke-gated |
| Provisioning cap (rule A's cap only) | smoke-gated |
| upgrade_hazard (one finite example) | smoke-gated |
| frozen_floor_not_monotone | compiled |
| emulation_repairs (sufficient condition) | compiled |
| marginal_match_insufficient | compiled |
| no_receiver_free_certificate | compiled |
| task_lt_reconstruction | compiled |
| DecisionDepth, CommValue, HoldFloor, Mixture, MismatchW1 | smoke-gated |

None of these is a closed-loop or return statement.

## 6. Not done at all

* P3 (external benchmark).
* NYC students.
* G3, G4 and G6.
* The PCT-proper receiver design.
* The selector co-adaptation hypothesis.
* The nesting lemma.
* Theory-section text.
* Comparison with published comm-MARL baselines.

## 7. Directions that can be followed

1. **Primary: the compatibility layer for mixed-version fleets.** E7 confirmation, then E9 exact protocol, costs, the
   nesting lemma, NYC / P3.
2. **Model-based input transport** (new, from G2c). In RI, a deterministic information-preserving map into the receiver's
   training support beat both plain and law-matching garbling. The E3 analogue is a learned "backward predictor" that maps a
   fresh copy to an older-looking one for the frozen receiver. Untested; novelty to check.
3. **Adaptation baselines as a deployment option.** FT-mix / PCT go in the decision table with their costs; PAIRED v2 (E10)
   stays a narrow side test.
4. **Rollout planning (G8).** Which receivers to update first, from mixed-fleet curves at 25 / 50 / 75 % old.

## 8. Dropped, and what each taught

| Dropped | Why | Lesson | Where it sits in the current picture |
|---|---|---|---|
| Learned selector / critic | No ranking signal (Spearman ≈ 0); the relay protocol later took the headroom | Learn where the protocol leaves room; check headroom first | The protocol layer is where the gains live |
| Input relabel / remap / clip / throttle / per-slot emulation | The receiver's support is a joint, history-level property; partial restoration is worse than none | Repairs must act at the protocol (history) level, or restore the input exactly | That is what EMU on U2 / E9 do |
| W1 law and scalar certificates | Distance predicts but is not a lever; certificates need the receiver | Support, not distance | Receiver-relative tools (detectors, emulators) |
| χ² Gaussian gate | Rank-deficient covariance | Standard detectors need care to be fair baselines | E8 |
| PAIRED v1 | Pairing halves the distinct states; teacher-relative h is weak | Simple replay fine-tuning (FT-mix) is a strong baseline | Adaptation is a cost option, not the method |
| "First to observe", "minimax", "exact", "iff" | Prior art (RDC); overclaims caught by audits and self-checks | Self-checks that can fail and external audits pay off | Claim map and wording table |
| NYC five-lane (and two-lane) run | RAM, then swap, then disk | Check memory per trainer before parallel launches | NYC needs a bigger machine |

## 9. Novelty: searches 03/10 18:5x and 23:4x, about 7 queries, not exhaustive

**Close prior art:**
* RDC (NeurIPS 2025): a drop when the delay improves, for policies trained under delay.
* Backward-compatible model updates: BCT, PCT / Focal Distillation, Gated Fusion, BCWI.
* Agent-replacement trust regions (TeamTR).
* Backward-compatible expansion of multi-agent systems (MonoScale: non-interfering additions).
* Protocol versioning in LLM-agent ecosystems (A2A version negotiation); legacy-compatible modes in wireless standards.
* Max-age-first AoI scheduling (Kadota et al.).

**Not found:**
* A learned-receiver MARL study in which a capacity upgrade breaks frozen receivers through the scheduler's broadcast history;
* the separation of "missing information" from "use" by a nested upgrade (N4);
* a compatibility layer (legacy-order schedule + packet-only emulator / legacy-state base packets) evaluated in mixed-version
  fleets against fallback, rollback, fine-tuning and retraining with costs.

**Verdict.** The defensible novelty is the problem + mechanism + compatibility layer + deployment comparison. It is not the
hazard itself, nor any generic "preserve old behaviour" technique.

## 10. Is the story good, and is it practical?

**Story (one line).** Upgrading the communication of a learned multi-agent system is not automatically safe. Frozen receivers
can fall below silence, not because they lose information but because the upgrade changes the history they were trained to
read. Keeping that history available (the compatibility layer) lets legacy receivers work unchanged while upgraded receivers
use the new capacity. In mixed-version fleets this beats fallback and rollback without retraining.

**Strengths.**
* There is a mechanism with an intervention (N4 + the emulator: +8.13).
* Exactness is checked by replay (E9).
* Strict baselines (Z, MASK).
* The cost table.
* An honest negative on the learned adaptation branch.

**Weak points, i.e. what reviewers will ask.**
1. **One simulator family.** CityFlow 3×3 / 4×4; NYC is blocked; P3 has not started.
2. **Our own teacher / students;** no published comm-MARL baseline.
3. **Effect sizes and seeds.** The mixed-fleet pilot has +2.4 over fallback with 5 seeds; confirmation is pending.
4. **Cost.** The upgraded channel delivers 7.5× K1's bytes.
5. **Realism.** Real deployments with an order-preserving legacy mode exist in spirit (backward-compatible modes in V2X / NR
   standards; staged over-the-air updates of signal controllers and vehicle fleets), but we do not use real traces.

**Where it is practical.**
* Staged updates of fleets: traffic-signal controllers, connected vehicles, robot teams.
* Firmware versions coexist, and some learned controllers are certified or frozen while the network is upgraded.
* The output an operator can use is a decision table:
  * keep the receiver with the compatibility layer, when the scheduler can keep the legacy order or state;
  * fall back, which is safe but gives up gains;
  * fine-tune, at about 80 episodes and teacher access;
  * retrain;
  * plus what each costs.

**What would make it clearly sufficient:**
* E7 confirmed with CIs and NEW-group non-inferiority;
* the nesting lemma compiled;
* one independent setting (NYC on a bigger machine, or the P3 benchmark);
* one published comm-MARL baseline run under the same upgrade.

> **Cập nhật 04/10 00:4x:** khẩu hiệu "Histories, Not Formats" được THAY bằng framing *Legacy-View Emulation for Mixed-Version MARL* — xem research/papers/audits/FRAMING_LEGACY_VIEW_20261004.md (phản hồi review HISTORY_FRAMING_REVIEW_20261004; A2A / Liskov–Wing / Abadi–Lamport là tiền lệ, không phải đối thủ yếu).
