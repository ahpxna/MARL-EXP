# E3 interim results (28/09/2026, 03:00) — gates G1/G2 for the actors finished so far

- Protocols: `PROTOCOL_E3_PILOT_20260928.md` (BC + MAPPO) and `PROTOCOL_E3_SCRATCH_20260928.md`
  (MAPPO from scratch), both written before these results.
- Development split 501–508 × headways 8, 16 (16 episodes, opened); `scripts/MARL_e3_message_use.py`.
- **Self-checks PASS for every actor:**
  - access invariants on every step;
  - about 1,600 undelivered-sender blocks verified to be the missing encoding.
- **Operational note.** The Mac slept between about 00:55 and 02:50. The runs paused and did not
  fail (the logs' clocks count only awake time). `caffeinate` now holds the machine awake for 12 h.

## Actors finished so far

| actor | select Σ waiting (MP2 1730) | G2 (≤ +10% of MP2) | dev: MP2 vs actor | none vs actual | stale | shuffle | full | input change (none / stale / shuffle) | G1 |
|---|---|---|---|---|---|---|---|---|---|
| BC + MAPPO seed 0 (**pilot gate**) | 1462 (BC only 1624) | PASS | +12.1% [+7.1, +17.0] | +0.41% [−2.12, +2.86] | +2.27% [−0.55, +5.12] | +2.13% [−0.03, +4.16] | +6.39% [+2.31, +10.05] | 0.25 / 0.16 / 0.20 | **FAIL** (closed-loop part) |
| BC + MAPPO seed 3 | 1451 (BC only 1648) | PASS | +14.0% [+8.2, +19.9] | +5.68% [+2.13, +9.59] | −0.98% [−3.26, +1.31] | +0.98% [−1.91, +4.00] | +12.86% [+7.29, +19.21] | 0.29 / 0.18 / 0.21 | PASS |
| scratch seed 3 | **1316** | PASS | **+23.1% [+14.7, +31.9]** | **+7.31% [+4.05, +10.62]** | +1.14% [−2.52, +4.58] | **+5.06% [+2.26, +7.91]** | +2.47% [−0.38, +5.41] | 0.53 / 0.38 / 0.43 | PASS |

Columns "MP2 vs actor" through "full" are the paired change in closed-loop Σ waiting against the
same actor's `actual` run. Positive means worse than `actual`.

## Reading, as the protocols fix it

1. **Competence (G2).**
   - Every finished learned actor beats MP2: select −15% to −24%, and on development MP2 is
     +12% to +23% worse, with every CI above 0.
   - This is development evidence on a fixed panel, not a test.
   - The actor is learned (MAPPO on the team reward), and the scratch actor is not warm-started
     from MP2.
2. **Message use (G1).**
   - **The BC + MAPPO pilot seed 0 FAILS the closed-loop part of G1.** Removing all messages does
     not measurably hurt it (+0.4%), although 25% of its input-level actions change.
   - By PROTOCOL_E3_PILOT §5, the BC chain's selector and closed-loop results are therefore
     RECORDED BUT NOT INTERPRETED as a method result.
   - Seed 3 of the same recipe does pass. Message use varies across seeds.
3. **The scratch actor (seed 3) uses messages clearly.**
   - Removing them costs +7.3%.
   - Scrambling sender identity costs +5.1%.
   - Its gates are per seed (PROTOCOL_E3_SCRATCH), so its downstream results will be read.
   - The protocol's scratch gate for interpretation is per seed, and seed 0 of the scratch chain
     is still training.
4. **"Full" communication (every receiver decodes all 8 senders) HURTS the BC actors** (+6% and
   +13%). They never saw full delivery in training (capacities ≤ 7). This is a train/test
   distribution shift, so more information is not automatically better for a fixed actor
   (PROTOCOL_HETERO_v0 Amendment 1).

## Still running (03:00)

- BC + MAPPO seeds 0–2: labels for seed 0.
- BC + MAPPO seeds 3–4: labels for seed 3.
- Scratch seeds 0–2: seed 0 is training.
- Scratch seeds 3–4: labels for seed 3.
- Gates full9, then OLD7b.

## Update 08:30 — hung CityFlow processes; learned SchedNet baseline (partial)

**Hang.** Every E3 Python process stopped writing between 00:56 and 03:18 and has since sat at
0% CPU in state S. The Mac was kept awake after 02:53, and the Lean gates kept running.
- `sample` shows the main thread blocked inside `cityflow.cpython-312-darwin.so` in
  `pthread_cond_wait`: the engine's thread barrier, holding the GIL.
- Threads are few (12–18 per process), so this is not a thread leak.
- Reading: a lost-wakeup deadlock in CityFlow's barrier, exposed by heavy CPU oversubscription
  (about 25 processes on 10 cores) and the system sleep.
- Earlier runs (thousands of replays, all closed-loop panels) never hung.
- **Fixes:**
  - `scripts/run_with_watchdog.py`: kills a child whose log is silent for S seconds, parks its
    partial output in `legacy/` and retries. Tested on hang, success and failure.
  - `scripts/RUN_marl_e3_resume.sh` and `RUN_marl_e3_schednet_resume.sh`: keep every finished
    stage and rerun the rest under the watchdog, with the ORIGINAL shard partition.
- The hung processes must be stopped first; the resume runners refuse to start while they are
  alive.
- **What was complete at the hang:**
  - BC s0: actor, message use, select labels, train shards 1, 3, 4.
  - BC s3: actor, message use, dev labels, all 3 train shards.
  - Scratch s3: actor, message use, select and dev labels, train shards 0 and 1.
  - Scratch s0: nothing (hung at iteration 485 of 2000).

**Learned SchedNet adaptation** (`scripts/MARL_e3_schednet_train.py`; sender-side 1 B weight from
its own sensor; Plackett–Luce PPO on the team reward; frozen scratch-s3 actor; pilot panel 901–916;
against the same actor's cached-queue prefix):

| init seed | Σ waiting vs prefix |
|---|---|
| s0 | +1.13% [−0.66, +2.93] |
| s1 | +1.90% [−0.13, +4.25] |
| s2 | hung, to be rerun |

- The learned scheduling order does not beat the cached-queue prefix; it is slightly worse and
  not significant.
- The same run for the BC-s3 actor has not started yet.

## Update 10:20 — ablation for the scratch s3 actor (gates G1/G2 pass; read per PROTOCOL_E3_ABLATION)

Closed loop, pilot panel 901–916, 32 episodes, +84 B, direct. Init seeds averaged per episode.

| variant | Σ waiting vs prefix | vs sel_nobid | edited steps / 26 | bytes/step |
|---|---|---|---|---|
| sel_nobid | −0.05% [−1.18, +0.98] | — | 8.5 | 205.6 |
| sel_bid | +0.00% [−0.93, +0.94] | +0.11% [−0.93, +1.21] | 10.3 | 218.3 |
| sel_resp | −0.41% [−1.65, +0.85] | −0.34% [−1.36, +0.65] | 13.9 | 213.6 |
| **sel_bid_resp** | −0.46% [−1.33, +0.41] | −0.36% [−1.24, +0.55] | 3.1 | 204.9 |
| MP2 reference | **+24.0% [+19.3, +28.8]** | | | |

**Offline, on held-out development labels** (48 states; direct).

| variant | realised gain |
|---|---|
| sel_nobid | −0.43 |
| sel_bid | −0.35 |
| sel_resp | −0.49 |
| sel_bid_resp | −0.19 |
| oracle over the same candidates | +15.44 |

**Response head, development.**

| head | accuracy | precision | recall |
|---|---|---|---|
| no bid | 0.893 | 0.43 | 0.006 |
| with bid | 0.895 | 0.53 | 0.15 |

Base rate 0.106.

**Reading.**
- The learned actor is strong: MP2 is 24% worse.
- The continuation-label headroom is large (+15.4 per state).
- No selector variant exploits it, even offline: all realised development gains are ≤ 0, and no
  closed-loop effect is significant.
- The bid does carry response information. It raises the head's recall from 0.006 to 0.15 and its
  precision from 0.43 to 0.53, but the critic does not turn that into value.
- Likely causes, not yet tested:
  - little data: 768 training states;
  - a very small select split: 48 states, for τ and epoch;
  - a noisier target than held phase.
- This is a development result, as PROTOCOL_E3_ABLATION says, and it is recorded as negative.
- **Next (a learning-curve step, not new features):** see PROTOCOL_E3_ABLATION Amendment 1.

## Update 10:30 — learned SchedNet v2 (genuine 1-byte weights); resume bug

**Learned SchedNet v2** (`e3_schednet_v2_20260928`; pilot panel 901–916; Σ waiting against the
same actor's cached-queue prefix):

| actor | init s0 | init s1 | init s2 |
|---|---|---|---|
| scratch s3 | +3.15% [+1.34, +4.95] | +0.36% [−1.42, +2.34] | +0.66% [−1.33, +2.75] |
| BC s3 | +1.59% [−0.44, +3.60] | +1.46% [−0.75, +3.77] | +4.83% [+2.21, +7.63] |

- A learned 1-byte sender-weight schedule never beats the committed cached-queue priority.
- It is significantly worse in 2 of 6 runs.
- The earlier v1 numbers (float weights) point the same way.

**Resume bug (fixed in `RUN_marl_e3_resume_v2.sh`).** For a freshly trained actor with no label
directory yet, the shard-count line failed under `pipefail` and `set -e` stopped the script
silently. BC seeds 1–2 were affected; they were retrained (s1 select 1490) and resumed with v2 at
10:26. BC s4 and scratch s0, s1, s2 and s4 still hit it in the running v1 lanes. They are resumed
with v2 once those lanes finish, because a running bash script must not be edited.

## Update 11:45 — BC chain frontier and shift (RECORDED, not read: BC pilot s0 failed G1); pkill; resumable labels

**Frontier** (v1 selectors, direct, pilot panel 901–916; Σ waiting against the actor's prefix).

| actor | selector | +28 | +56 | +84 | +140 |
|---|---|---|---|---|---|
| BC s0 | sel_bid | +0.8% (n.s.) | +2.8% | +2.9% | +2.7% |
| BC s0 | sel_nobid | +0.6% (n.s.) | +1.4% (n.s.) | +2.0% | +2.3% |
| BC s3 | sel_bid | +0.2% (n.s.) | +2.0% | +2.3% | +2.1% |
| BC s3 | sel_nobid | +2.8% | +4.0% | +3.2% | +3.3% |

- "n.s." marks a CI that covers 0; every other CI is above 0.
- Once the cap allows many edits (+56 and up), the selectors make things WORSE than the prefix.

**Shift** (+84; MP2 against the actor's prefix).

| actor | held-out headway 12 | bursty capacities, headway 8 | bursty capacities, headway 16 |
|---|---|---|---|
| BC s0 | +22.8% | +19.0% | +13.4% |
| BC s3 | +25.6% | +21.0% | +13.6% |

- All CIs are above 0, so the learned actor's advantage over MP2 survives the load and capacity
  shifts.
- The selectors stay at or above the prefix.

**pkill at 11:37.** `pkill -9 -f "scripts/MARL_e3_"` stopped the 8 deadlocked processes and also the
relaunched ones:
- the dense labels of scratch s3;
- BC s1's labels;
- scratch s4's training.

**Resumable labels.** `scripts/MARL_e3_continuation_labels_v2.py` resumes a directory in place,
keeping every complete state. Its rng consumption matches v1.
- Test: a resumed run's lines are IDENTICAL to an uninterrupted run's, and self-check PASS.
- The dense labels resumed with 1,170 of about 3,040 states already done.
- The dense and resume_v2 runners now use it, and the watchdog restarts in place.

## Update 11:47 — BC s0 ablation (RECORDED, not read)

Closed loop, pilot panel 901–916, +84 B, direct.

| variant | Σ waiting vs prefix | vs sel_nobid |
|---|---|---|
| sel_nobid | +1.97% [+0.37, +3.61] | — |
| sel_bid | +2.91% [+1.00, +5.04] | +0.91% |
| sel_resp | +2.04% | +0.12% |
| sel_bid_resp | +1.85% [+0.57, +3.17] | −0.04% |
| MP2 | +16.1% | |

Every selector variant is significantly WORSE than this actor's prefix. The variants do not differ
from each other. The same pattern holds for scratch s3 (all ≈ 0) and in the BC frontier (≥ +56).

## Update 12:15 — why the selectors do not help (diagnostic, scratch s3; `e3_selector_diag_scratch_s3.json`)

Producer `scripts/MARL_e3_selector_diag.py`: anchored critic predictions against the true continuation
gains on every feasible candidate of the select and development states, for all 12 trained selectors
(4 variants × 3 seeds).

| quantity | value |
|---|---|
| within-state Spearman correlation, development | −0.02 to +0.04 for EVERY selector |
| empirical ε, select, q50 | about 3.0 |
| empirical ε, select, q90 | 12.3–13.7 |
| mean best available gain, development | 15.4 |

**Reading.**
- The critic has essentially no ability to rank candidates within a state for the learned actor.
  Its error is of the order of the gains themselves.
- Editing on such scores is editing on noise, which explains the closed-loop harm at larger caps.
- The theory's safe rule (edit only if the estimated gain exceeds 2ε; `LeanMarlSafeEditV1`, gate
  pending) never edits here, because 2ε ≈ 26 exceeds the gains. It avoids harm and gains nothing.
- The E3 selector question is therefore an ESTIMATION problem. It is not a headroom problem: the
  oracle gain is +15.4 per state.
- The dense-label step tests whether more data reduces ε.

## Update 12:25 — communication delay acting on traffic (PROTOCOL_E3_DELAY_ACQ part A; `e3_delay_20260928`)

Payloads reach receivers d steps late (10 s per step); the prefix scheduler, capacities and bytes are unchanged.
Pilot panel 901–916, 32 episodes. **Self-checks PASS:** at d = 0, both the encoding and the MP2 identities held on
every step. Changes in Σ waiting are paired by episode.

| d | scratch s3 vs its d0 | BC s3 vs its d0 | MP2 vs its d0 | MP2 vs scratch s3 (same d) | MP2 vs BC s3 (same d) |
|---|---|---|---|---|---|
| 0 | — | — | — | +24.0% [+19.3, +28.8] | +16.1% [+12.8, +19.4] |
| 1 (10 s) | +0.3% [−1.7, +2.3] | −0.9% | −3.2% [−5.8, −0.7] | +19.5% | +13.0% |
| 2 (20 s) | **+3.9% [+1.8, +6.2]** | −1.2% | −4.2% [−6.6, −1.7] | +14.3% | +12.4% |
| 3 (30 s) | **+5.6% [+3.3, +8.3]** | −0.4% | −6.7% [−8.9, −4.3] | +9.5% [+5.8, +13.1] | +8.4% [+6.9, +9.9] |

**Reading.**
- The message-using scratch actor degrades as information ages, consistent with its G1 pass.
- The BC actor is insensitive to delay.
- The learned actors' advantage over MP2 shrinks with delay (24% → 9.5% at 30 s) but stays significant.
- **Unexpected:** MP2 IMPROVES with delay. Its use of the delivered downstream queues seems to hurt in this
  setting. This is recorded as an observation, not explained; with d > t no message exists at all, so part of
  the effect may be MP2 without downstream terms.
- Scope: a deterministic delivery delay only; no loss, jitter or bandwidth queue.

## Update 12:25 — step-3 audit fixes, measurement (`scripts/MARL_e3_selector_diag_v2.py`)

The auditor's four points were verified in the code:
- v1's rank correlation ignored ties; **95.8%** of candidate values tie with another in the same state;
- `edit_rate` counted gain ≠ 0;
- the τ grid had no "always keep the prefix" option (+∞), and `None` meant −∞ at runtime;
- the actor was trained with the prefix scheduler only.

**Recomputed from the checkpoints and labels (scratch s3, development, 12 selectors, no rollouts).**

| quantity | value |
|---|---|
| Spearman with ties | −0.04 to +0.04 |
| pairwise order accuracy on candidate pairs whose true gains differ | **0.40–0.48, below chance** |
| edit rate (chosen ≠ prefix) | 0.08–0.85 |
| harmful-edit rate given an edit | 0.43–0.75 |
| realised gain (bootstrap over episodes) | −0.98 to +0.31 (every CI covers 0) |

The diagnosis "the critic cannot order candidates" survives the corrected measurement.

**Corrections of my earlier wording.**
- The q90 of the gain error is a DIAGNOSTIC, not a certified ε.
- It is a gain error, while `LeanMarlSafeEditV1`'s ε is per value (a per-value ε implies a gain error of
  at most 2ε).
- So "the safe rule never edits here" is not a Lean-backed statement about these data. The paper
  wording is corrected accordingly.

## Update 12:45 — handoff F2-A (privileged-joint diagnostic) and F4 (delay v2)

**F2-A** (`selectors_v3`, scratch s3, development 48 states; the three init seeds averaged per state; bootstrap
over episodes):

| evaluator | development realised gain |
|---|---|
| legal, bid + head | −0.19 [−1.18, +0.84] |
| privileged, bid + head + joint actions | +1.42 [−1.06, +4.23] |
| privileged, joint actions only | +1.93 [−0.53, +4.88] |

- Privileged-only minus legal: **+2.12 [+0.10, +4.49]**. Privileged + bid + head minus legal: +1.61 [−0.41, +3.79].
- Tie-aware Spearman: 0.07–0.12 privileged, against about 0 legal.
- Harm given an edit: still 0.39–0.48.

**Reading.**
- Knowing the actor's actual response helps, so response information is PART of the bottleneck.
- Even the privileged evaluator reaches only about 12% of the +15.4 oracle headroom, so response
  information alone does not close it.
- By the handoff's rule, this justifies the ONE grounded adaptation F2-B: a multi-class response head
  (`scripts/MARL_e3_selector_train_v5.py`, running). It predicts which phase the actor plays and
  gives the critic the legal analogue of the privileged features.

**F4, delay v2** (`e3_delay_v2_20260928`): the causality assertion held on every step (every payload
used at step t was measured by the time of step t − d). All numbers are identical to v1. The scope stays a
delayed-observation stress test.

## Update 12:40 — F3 same-byte bid, F4 acquisition v2, F5 bridge (partial); scratch s3, development

**F3, same-byte bid** (`selectors_v4`; realised development gain, 3 init seeds each, direct; oracle +15.4).

| selector | s0 | s1 | s2 | mean |
|---|---|---|---|---|
| no bid | −0.48 | +0.17 | −0.98 | −0.43 |
| top-2 response bid (10 B) | −0.56 | −0.29 | −0.21 | −0.35 |
| queue bid (10 B) | −0.06 | −2.06 | −0.42 | −0.85 |

No bid helps, and the response bid is not better than the same-byte queue bid.

**F4, acquisition v2** (legal 2-bit gap bins; B = 24 per training state; provenance in
`acquisition_v2/acq_manifest_*`; realised development gain).

| strategy | s0 | s1 | s2 | mean |
|---|---|---|---|---|
| full (reference) | +0.00 | +0.31 | −0.88 | −0.19 |
| singleton | −0.21 | +0.12 | −1.17 | −0.42 |
| uniform | −1.29 | −0.71 | −0.92 | −0.97 |
| targeted | −2.08 | −1.29 | −0.62 | −1.33 |

- No acquisition strategy yields a useful evaluator. Targeted (near-tie receivers first) is the worst.
- There is no evidence that decision-targeted labelling helps here. The controlled E1 counterpart was
  a negative control, targeted ≡ uniform.
- The v1 run (`acquisition/`, full gap = privileged acquisition) is kept and labelled.

**F5, bridge panel** (`e3_bridge_20260928`, 4 of 16 states so far; one receiver, all 254 subsets).

| quantity | value |
|---|---|
| exact η* on the whole small space | 2.0–7.5 |
| hTop (deployed prefix = top-k by the fitted scores) | **FALSE in all 4 states** |
| geometric loss at R1 | 0 in all 4 states |
| T1 bound at R1 | 4–15 |

- On the actor-realised object, T1's hypothesis fails for the deployed cached-queue order.
- Even formally the bound is far from the realised loss, which is zero here.
- To be completed on all 16 states before any reading.

**F2-A replicated on BC s3** (development; oracle +12.33).

| evaluator | development realised gain |
|---|---|
| legal bid + head | **−1.31 [−2.32, −0.20]** |
| privileged + bid + head | +0.62 |
| privileged only | +1.48 |

- Privileged + bid + head minus legal: **+1.94 [+0.31, +3.97]**.
- Privileged only minus legal: **+2.79 [+1.02, +4.73]**.
- The pattern holds on two independently trained actors: response information is part of the
  bottleneck, and it closes only about 12–20% of the headroom.
- F2-B is run on both actors.

**F4 acquisition v2 on BC s3** (development; oracle +12.33; realised gain, mean of 3 seeds).

| strategy | mean |
|---|---|
| full | −1.31 |
| singleton | −1.22 |
| targeted | −1.42 |
| uniform | −2.34 |

No acquisition strategy helps on either actor. This closes F4's acquisition item as a negative result.

## Update — F5 bridge panel complete (`e3_bridge_20260928`)

Setup: 16 development states, scratch s3 actor. One receiver per state (the smallest bid gap); all 254
subsets of its senders were evaluated with the continuation value; the other receivers keep the prefix.

| quantity | value |
|---|---|
| exact ScoreLocal η* on the whole small space | median 6.25, range 2.0–16.5 |
| mean spread of f over k-sets | 9.6 |
| hTop (the deployed cached-queue prefix is top-k by the fitted scores) | **false in 16/16 states** |
| single-receiver headroom V_all − f(P) | mean 4.44, max 13 |
| geometric loss at R1 | mean 0.31; R1 reaches V_all in 15/16 states |
| geometric loss at R2 | 0 (reaches V_all in 16/16) |
| T1 bound at R1 | mean 6.62 (in the one state with a loss, the bound is 2× the loss) |
| byte-feasibility loss (+84 B) | 0 in all states |
| candidate-coverage loss | mean 0.31 (the family contains the optimum in 15/16) |

**Reading, for this reduced actor-realised object.**
- The loss decomposition assigns almost nothing to commitment geometry, the byte cap or candidate
  coverage: one revision already contains the optimum.
- Essentially all of the deployed selectors' loss is evaluator/estimation loss. This agrees with the
  diagnostics: pair-order accuracy below chance, and harm given an edit around 0.5.
- T1's hypothesis (hTop) never holds for the deployed order.
- η* is of the order of the whole value spread, so the T1 bound has little explanatory power here.
- The theory–traffic bridge is therefore answered NEGATIVELY for this object. The conditional
  theorem stands; it does not explain the traffic results.

## Update about 13:17 — self-audit corrections, F2-B (multi-class head), F5 bridge v2

Self-audit ledger: `research/papers/audits/MARL_SELF_AUDIT_LEDGER_20260928.md`. The entries used here are
L-01..L-05, L-14 and L-34.

**Paired development comparison tool.** `scripts/MARL_e3_paired_eval.py` (read-only). It averages the
three init seeds per state and bootstraps over episodes and, as a sensitivity check, over TRAFFIC SEEDS
(both loads of a seed together). It reproduces the F2-A numbers above exactly, which is its self-check.

**Correction to F2-A (L-05).** On scratch s3, "privileged-only − legal = +2.12 [+0.10, +4.49]" is significant
with the episode bootstrap only. Clustered by traffic seed the interval is [−0.21, +4.56]. On BC s3 the
difference stays significant: +2.79, seed interval [+1.11, +4.68].

**F2-B, multi-class response head** (`selectors_v5`, legal inputs; development, 48 states per actor;
`f2b_paired_dev.json`).

| actor | legal (bid + binary head) | multi-class head + bid | multi-class head, no bid | privileged only |
|---|---|---|---|---|
| scratch s3 | −0.19 | −0.78 | −0.15 | +1.93 |
| BC s3 | −1.31 | −0.90 | −2.28 | +1.48 |

- Multi-class minus legal: −0.60 [−1.53, +0.30] and +0.03 on scratch s3; +0.41 [−1.08, +1.94] and −0.97 on
  BC s3. None is significant.
- Privileged minus multi-class (with bid): +2.72 [+1.03, +4.77] and +2.38 [+0.93, +3.69], significant under
  both bootstraps.
- The head predicts the actor's phase correctly on 44–48% of the (candidate, receiver) pairs whose action
  changes. That is information, but the critic does not turn it into choices.
- **Reading:** the one grounded adaptation of handoff F2-B is NEGATIVE on both actors. By the handoff's rule
  there is no closed loop, because the development selection did not improve.

**All evaluator arms on the same states** (`e3_dev_arms.json`, 8 arms × 2 actors). Every legal arm is
between −2.34 and −0.19. Of the 21 legal pairwise differences per actor, one is significant (BC s3:
uniform acquisition − multi-class head = −1.44 [−2.15, −0.79]).

**F5 bridge v2** (`scripts/MARL_e3_bridge_panel_v2.py`; `e3_bridge_v2_scratch_s3_20260928` and
`e3_bridge_v2_bc_s3_20260928`; self-check PASS, including `score_frontier` asserted on the data).

What v2 fixes relative to v1:
- the empty set and the full set are included (256 contexts, 1,024 ScoreLocal pairs);
- η_top (ScoreLocal AND hTop at one w) is solved by an LP;
- d is minimised over the optimal k-sets.

| quantity | scratch s3 | BC s3 |
|---|---|---|
| hTop satisfiable at the optimal constant (η_top = η*) | **5/16** | **5/16** |
| η* median [range] | 6.25 [2.0, 16.5] | 5.0 [0.5, 18.0] |
| η_top median [range]; mean η_top − η* | 7.0 [3.0, 19.5]; 1.38 | 6.0 [0.5, 18.5]; 1.44 |
| spread of f over k-sets (mean) | 9.6 | 8.5 |
| optimum within one revision (d_min ≤ 1) | 15/16 | 13/16 |
| geometric loss R1 (mean) / R2 | 0.31 / 0 | 0.75 / 0 |
| valid T1 bound 2η_top(d−R)₊ at R1: nonzero states, (loss, bound) | 1: (5, 14) | 3: (7, 23), (2, 12), (3, 20) |
| byte loss (+84 B) | 0 | 0 |
| candidate family contains the optimum | 15/16 | 13/16 |

**Correction (L-34).** v1's "hTop false in 16/16" is WITHDRAWN. It came from reading one minimiser of a
non-unique LP (L-02). The corrected facts are:
- the deployed prefix satisfies T1's hypotheses at the optimal constant in 5 of 16 states per actor;
- the valid bound holds everywhere;
- the bound is zero where the optimum is within R;
- where the bound is nonzero, it is 3–7× the realised loss.

**Reading.**
- Geometry, bytes and coverage cost little and are correctly bounded on these reduced objects.
- η is of the order of the value spread, so first-order scores explain the values poorly.
- The loss of the deployed selectors is estimation, which T1 names (2ε) but cannot bound for a learned
  critic.

## Update 13:26 — traffic-seed cluster sensitivity; closed loop v4; BC s4 labels

**Seed clusters** (`e3_seed_cluster_20260928.txt`; every panel has 2 episodes per traffic seed). Of 109 closed-loop
and message-use endpoints, two change significance:
- BC s3 frontier +56 sel_bid: +1.95%, significant by episode, **n.s. by traffic seed** [−0.30, +4.01];
- BC s0 shuffle: +2.13%, becomes significant by seed. It is not a gate quantity.

Unchanged under seed clusters:
- G1 for every actor (scratch s3 `none` [+4.2, +10.3]);
- MP2 vs every actor;
- the scratch s3 closed loop (all n.s.);
- delay (scratch s3 at d3 [+3.4, +8.1]);
- SchedNet (2 of 6 significant).

**Closed loop v4** (`scripts/MARL_e3_closed_loop_v4.py`): v3+ selectors (τ strings), the queue bid and the
multi-class head can now be deployed. Its self-checks match the trainer path exactly, and a smoke run
reproduces v3's rows.

**BC s4 labels.** Train shards 1 and 2 died under producer v2 (FileExistsError on a watchdog restart). They
were relaunched in place with v3 at 13:25.

## Update 14:13 — independent recheck P0/P1: runtime parity, label integrity, resumable actors, seeds

**Runtime parity (P0).** `scripts/MARL_e3_closed_loop_v5.py`. v4 is kept because its smoke run is an artifact.
- τ parsing is strict: NaN, a bare 'inf', unknown strings and None in a v3+ checkpoint are all rejected.
- Selftest PASS: 7 decision cases, including an exact tie at τ, +∞ with huge scores, no feasible edit, and
  argmax ties.
- Per-step byte parity is asserted: the env's accounted bytes equal the scheduler's scored bytes.
- Runtime scores and choices equal the trainer path for v2–v5 selectors.
- Development smoke `e3_clv5_dev_smoke_140422` (seed 501, 10 methods) PASS. Test seeds were never used.

**Label integrity (P1).** `scripts/MARL_e3_labels_audit.py` gives `e3_labels_audit_v2_20260928.{json,txt}`: 39 label
dirs (dense, scratch s3, BC s0/s1/s3/s4), all PASS.
- Nothing is wrong at the key level: 0 missing (complete dirs), 0 extraneous, 0 lost from partials, 0 duplicates,
  0 content conflicts between copies, 0 mid-stream JSON errors.
- Nothing is wrong at the record level: every record passes the semantic checks.
- Self-check provenance holds: every final key has a production line with no new failure, or its dir is a
  single-attempt run covered by its manifest.
- The v3 recomputation of a v1 dense state is identical.

**Resumable actors.** Scratch s4 lost ~1,640 iterations to three hangs and is on its last retry.
- `scripts/MARL_e3_actor_train_resume.py` writes atomic full-state checkpoints and resumes in place. It is
  BITWISE-equal to the protocol trainers, uninterrupted and stopped-then-resumed, for both scratch and mix.
- Replicas for scratch s0, s1, s2 and s4 run in `e3_scratch_rs_20260928`. The run-of-record rule was written
  before launch.
- Live check: the replicas print identical traces to the lane runs (s4 77/77 iterations, s0 76/76).

**Seeds.** `PROTOCOL_DEVIATION_E3_SEEDS_20260928.md` (dated, not backdated) lists every seed and failed attempt,
with 7 binding reporting commitments.

**F6.** `PROTOCOL_E3_FINAL_DRAFT_20260928.md` is a DRAFT, not frozen. The endpoint type and margin are OPEN (the
authors' decision). Test seeds stay closed.

## Update — F5b, multi-receiver loss decomposition (`e3_mrdecomp_20260928`; independent recheck §1 scope)

Setup:
- 48 development states per actor.
- The candidate families of the labels, which edit many receivers at once (the family best edits ~5.7).
- The arms' actual choices (`dev_chosen`).
- A rollout local search over single sender swaps at any receiver, within +84 B, started from the family best
  and from the prefix. This is a diagnostic that uses the simulator.
- Self-checks: every replayed value equals the stored labels; every searched profile is legal.

Results (scratch s3: 47/48 states, the last reruns after a CityFlow deadlock; BC s3: 48/48).

| term (mean, episode CI) | scratch s3 | BC s3 |
|---|---|---|
| best found over prefix | +19.8 [16.0, 23.7] | +16.0 [13.8, 19.3] |
| coverage outside the family (lower bound) | +4.5 [3.2, 5.8] | +3.7 [3.2, 4.3] |
| R1 restriction inside the family | +2.6 [1.6, 3.6] | +2.5 [1.5, 3.7] |
| byte cap | +0.06 | +0.12 |
| legal bid+head: realised / estimation loss | −0.22 / +15.5 | −1.31 / +13.7 |
| privileged (diagnostic): realised | +2.0 | +1.5 |
| local search from prefix: gain (share of best); swaps; receivers | +17.4 (88%); 2.6; 2.5 | +13.8 (86%); 2.3; 2.2 |
| multi-receiver edits super- / sub-additive | 21 / 15 of 39 | 19 / 12 of 38 |

Traffic-seed intervals are in the report JSON and agree.

**Reading.**
- Estimation is the dominant loss on the tested multi-receiver objects.
- Unlike the single-receiver F5 panel, coverage and bounded revision are NOT free once all receivers move.
- The receivers interact.
- A few swaps (about 2–3) from the prefix would capture most of the headroom. Choosing them from legal
  information is the unsolved part.

**F5b final (15:15, `e3_mrdecomp_20260928/report.json`).** Scratch s3 is now 48/48; its last shard reran after the deadlock.
- Scratch s3: best found +20.1 [16.3, 23.8]; coverage ≥ +4.65 [3.4, 5.9]; R1 +2.7 [1.7, 3.7]; bytes +0.06; legal realised −0.19 (equal to
  the paired eval), so estimation is +15.6 [12.9, 18.3]; local search from the prefix +17.6 (88%) with 2.6 swaps on 2.5 receivers;
  22/40 multi-receiver edits are superadditive.
- BC s3: unchanged from the table above (it was already 48/48).
- The reading is unchanged.
