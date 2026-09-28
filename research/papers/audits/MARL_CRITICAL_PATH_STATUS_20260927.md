# Critical path status vs `MARL_SUBMISSION_CRITICAL_PATH_20260927.md` — 27/09/2026, updated 23:50

- Read line by line against the artifacts. This file is not a ledger.
- **Update 23:50.**
  - The 23:35 version is archived at `legacy/MARL_CRITICAL_PATH_STATUS_20260927_v2335.md`.
  - The independent recheck (`MARL_CRITICAL_PATH_INDEPENDENT_RECHECK_20260927.md`) was verified
    against the code, and its corrections are applied below:
    - the η bridge is a one-swap diagnostic;
    - the request baseline leaked the exact gap (fixed in v4);
    - the baselines are heuristics;
    - latency is compute only.
  - New results are in `research/marl_budget/BASELINES_DIRECT_STAGEA2_RESULTS_20260927.md`.
- Legend: ✅ done (artifact named) · 🟡 partly done or pending a running job · ❌ not done ·
  ⛔ dropped or reframed because evidence forced it.
- The critical path was written at 14:11. Later independent audits (cheap-checks v2, hetero
  diagnostic, B1 verdict, E1) changed the setting. Those changes are recorded below as reframings
  where they apply.

## §3 Items the auditor handed over

| item | status |
|---|---|
| `models/marl_revision_selector.py` (exact F_R enumeration, 4 tests) | ✅ exists and is tested. The hetero protocol uses its own legality check (`check_legal`) and a candidate family, because exact enumeration over 9 receivers is infeasible. This is labelled "candidate-set argmax" everywhere, as §4 step 3.3 allows. |
| `LeanMarlRevisionAuditBridgeV1` (`deployed_regret_feasible`, +2e/+4e transfer) | ✅ compiled; smoke-gated in `smokeMARL17` (PASS). |
| Paper B supplement sentence (η ~ h) | 🟡 the other session's edit is still awaiting the user's keep/revert decision. |

## §4 Step 1 — lock the protocol and fix the common measurement: ✅ (for the reframed protocol)

1. **Network-wide broadcast set.** ⛔→✅ reframed. Under the global-broadcast protocol (PROTOCOL_v1)
   the cheap checks found:
   - nesting is nearly free: best nested chain regret 0.33 against 23.1 for the heuristic prefix;
   - tabulation dominates prepared priority in value, at equal latency;
   - revision helps only a worse score.

   The mechanism was therefore studied where nesting is FORCED: one broadcast stream,
   heterogeneous receiver capacities (`PROTOCOL_HETERO_v0`). That protocol is named as a
   different model, as step 1.1 requires.
2. **f_joint.** ✅ Every hetero label is the value of the JOINT action when all receivers act on
   their restricted views together.
3. **Pre-grant context z.** ✅ Paid cache and time, plus the legal receiver mirror
   (mirror = caches is asserted after every transmission). Bids are charged inside the same
   total cap (B2), and the same-byte `bid_queue` comparator has equal rights.
4. **Raw storage.** ✅ Masks, sender IDs, joint actions, values, seeds, horizon; source hashes in
   every manifest. Since the B1 verdict, every job also saves its model, τ, chosen indices and
   gains.
5. **Oracle separation.** ✅ `no_oracle_access` wraps every live step and fails on any oracle call.
   The closed-loop report checks that the access logs of every deployable method are zero.
6. **Small scene first.** ✅ Smoke and mini runs precede every run. The live panel collector was
   checked to reproduce the replay pipeline exactly on seed 301.

## §4 Step 2 — train an actor with real messages, then freeze it for E2: ❌ NOT DONE

- Every selector result uses the frozen max-pressure actor (MP2). No learned actor exists.
- The step was postponed, not dropped:
  - the audits first asked to settle whether a legal selector can exploit the headroom at all
    (B1, B2);
  - the user's current instruction is to wait for the B4 closed-loop result before E3.
- **This blocks the submission** (the critical path's own §5 table: "Learned actor and
  evaluator — Chặn: Có").

## §4 Step 3 — evaluator, selector and strong comparators on the same actor: 🟡

**3.1–3.2 Learned evaluators on permitted context, episode splits.** ✅ Frozen MP2 is the actor.
- B1 learning curve.
- Mitigation screens (10+ directions).
- B2 (charged receiver-local bids): **PASS on fresh seeds**, +1.85 [+0.95, +2.84] over the better
  no-bid legal control, at 18% of the oracle.

**3.3 R = 0/1/2.** 🟡 A candidate family is used (every one-swap, 24 random with R ≤ 1, 24 with
R ≤ 2, 24 unrestricted), not exact enumeration.

**3.4 Baselines.**

| baseline | status |
|---|---|
| score-priority prefix | ✅ |
| score + matched local search | 🟡 hetero pilot only (`learned_R1` coordinate search against `direct_unrestricted`) |
| direct budget-conditioned selector | ✅ (development) independently tuned, epoch selected on the direct +84 metric (`direct_indep_*`). It does not change the +84 point (−0.25 [−1.16, +0.61]). **R1 does not beat it** (direct − R1 = +1.1 to +1.6, CI > 0, at +56/+84/none). The bid advantage survives: +1.28 [+0.11, +2.60]. |
| SchedNet / Where2comm | 🟡 **heuristics only**. `schednet_fresh` (hand-set fresh-queue weight) is WORSE than the prefix in closed loop (+4.7% Σ waiting). `where2comm_top2_bin` (rule on the 1 B bid, corrected v4) gives +0.5% at +25% bytes. Learned adaptations are ❌ and need the E3 actor/critic loop. |
| retrospective exhaustive oracle | ✅ `hetero_exact`; oracle over candidates |
| random / full / no communication | 🟡 private/unrestricted oracle only |

**3.5 Decomposition** (score error, priority gap, evaluator, search). ✅ For global broadcast
(cheap checks v2) and the hetero exact oracle. 🟡 Not yet redone for the B2 method.

**3.6 Latency, bytes, deadlines.**
- Bytes ✅.
- Post-grant latency ✅ for PROTOCOL_v1: this is the refutation of the latency premise.
- 🟡 B2 method latency is measured, COMPUTE ONLY (`latency_b2_20260927_232749`):
  - median 16.6 ms, p95 17.9 ms, max 48 ms;
  - it was measured under CPU contention from three other jobs, so it is upward-biased;
  - no bid uplink round, no network delay;
  - 0% misses at 50 ms is therefore not an end-to-end guarantee.
- The baselines' latency is not measured.

**3.7 Delay consuming simulation time.** ❌ Zero delivery delay only.

**Done criterion** ("paired pilot showing repair useful + its latency cost"). 🟡
- Held phase: yes (B2).
- **Closed loop: B3 FAIL.** −0.26% [−1.20%, +0.62%] against the control, while the oracle gets
  −14.5%.
  - Diagnosed as covariate shift induced by the policy itself: parity holds to 5e-6; the shadow
    run would edit at 13–16 of 16 steps, but the live selector stops editing.
- **Second fresh panel 1101–1116** (descriptive, not preregistered): the frozen B2 design gets
  −0.28% [−1.65, +1.18] against the prefix. It edits 1–3 of 26 steps, against 19 for the oracle
  (−14.4%). Same symptom as B3.
- **B4 (DAgger)**: retraining is done for top2_joint; the controls are still training at 23:50.
  The closed-loop dev and the test on 801–816 follow.
- Latency: compute only (see 3.6).

**If the budget-conditioned selector is as good or better:** ⛔ applied. The claim of practical
superiority of a precommitted priority was dropped for the global-budget protocol.

## §4 Step 4 — E1 controlled calibration: ✅ (with corrections)

- **E1a**, the exact T2 needle model: measured cost lies between the proved bounds.
- **Symmetric-design starvation**, as proved.
- **E1b**, the executable Bayes-decoder task: a crossover in R versus N.
- **Corrections after the E1 independent audit:**
  - E1b is separated from the Gaussian channel (witness cited);
  - the R2 crossover is described as a strategy result, not "rights make learning harder";
  - targeted ≡ uniform is marked as a negative control;
  - the adaptive curve is marked exploratory;
  - nominal N is labelled;
  - two-stage v2 uses a literal decoder;
  - figures v2 (`figures_20260927_v2`).
- **Not done (optional):** the certified finite-table construction (step 4.5).

## §4 Step 5 — main learned-MARL runs and acquisition ablation: ❌ (mostly), 🟡 (pieces)

- **Learned-actor runs with 5 training seeds:** ❌. They depend on step 2.
- **Fixed / bursty / shifted grant traces:** 🟡.
  - The capacity panels (fixed, bursty, low, high) and held-out loads (headway 12, 24, 5) are
    collected (B6).
  - Evaluated in the held phase, descriptively (`B5_B6_RESULTS_20260927.md`):
    - the design keeps its advantage under heavy/light held-out load, although load_12 is negative
      in point estimate;
    - it does not transfer to the fixed, bursty or low capacity processes.
    - This is not closed-loop robustness.
  - Correction: every earlier hetero panel used i.i.d. uniform capacities; the "bursty"
    BudgetTraceSpec is overwritten by the hetero capacity trace.
- **SchedNet adaptation:** 🟡 heuristic only (see 3.4). The learned adaptation is ❌.
- **Main outcomes:** ✅ the closed-loop report now covers Σ waiting, throughput,
  finished/unfinished, travel time of finished trips (biased) AND CityFlow's censored travel time,
  bytes, and an oracle-access self-check (`MARL_hetero_closed_loop_report.py`; B3 reported).
- **Pareto (quality against bytes and latency):** 🟡 working version
  `figures_20260927_v3/fig3_closed_loop_cl_baselines_20260927_232931.png`.
  - Closed loop, 32 episodes, episode CIs.
  - Direct selectors shown; the heuristic baselines are labelled as such.
  - Latency panel: prefix and B2 only.
  - To be redrawn after B4.
- **Traffic acquisition ablation:** ❌. Only the controlled one (E1b, fig4) exists.

## §4 Step 6 — assemble the submission: ❌ (Lean ✅)

- **Formal checking:** ✅. Gates PASS:
  - `smokeMARL17` (146 modules, 1298 theorems);
  - `smokeMARL4` (BlockFrontier, Starvation, CalibrationGap, PairCalibration);
  - `smokeMARL1_E1b` (E1bRealization).
- **Figures:**
  - fig1 ✅ (oracle best-gain illustration);
  - fig2 ✅;
  - fig4 ✅ (controlled only);
  - fig3 🟡 (old pilot panel).
- **Manuscript:** ❌ not started. No MARL claim enters a manuscript before its gate and its
  experiment exist.

## §5 table ("hard items")

| item | blocks? | status |
|---|---|---|
| Actor/observation realization T1 | yes | 🟡 the E1b mean value is proved (`LeanMarlE1bRealizationV1`, ScoreLocal f g² β²). **Traffic: NOT bridged (corrected 23:50).** `eta_bridge_20260927.json` fits only one-swaps around P, so its η is a LOWER bound on the global η and certifies nothing. Correct labels: one-swap additive residual zero in 75.7%; fitted local no-improvement 63.3%; direct local statement (no one-swap improves) 72.5%. Counterexample to reading it as a certificate: f = 1 iff {2,3} ⊆ S. |
| Valid output F_R | yes | ✅ AuditBridge `deployed_regret_feasible` (gated); env `check_legal` on every submission |
| Learned actor and evaluator | yes | evaluator ✅ · actor ❌ |
| δ_U from data | certified claim only | not certified; empirical only (as allowed) |
| Actor drift | no (frozen rounds) | ✅ frozen rounds |
| T2 compile | yes | ✅ gated |
| T2 log-cardinality gap | no | ✅ beyond requirement: CalibrationGap (Θ(M log(M/α)) for fixed schedules) and the two-stage numerical |
| Near-tie / multiple answers | no | hSep kept ✅ |
| Shared-pair interactions | no | ✅ beyond requirement: PairCalibration lower + legal upper; tightness open |
| Uniform all-budget table | no | ❌ (post-submission, as the doc says) |
| Near-optimal proxy starvation | strong A claim only | 🟡 conditional Starvation theorems; the strong A claim is not made |
| Optimal-decoder monotonicity | no | `e1b_mono` ✅ (not needed) |

## Items dropped or reframed because evidence forced it (bỏ bất đắc dĩ)

1. **"A prepared priority is faster than table lookup / has a practical advantage."** Refuted by
   measurement (post-grant 0.1 µs for tabulation against 0.3–0.5 µs for the prefix). Dropped.
2. **Global broadcast as the main learned-selector setting.** Nesting is nearly free there, so the
   setting was moved to heterogeneous receivers, where nesting is forced. Reframed.
3. **"Certified no-repair" for the neural selector.** No uniform coverage exists. Dropped, as the
   critical path anticipated.
4. **"Legal information is insufficient in principle."** Replaced by the weaker supported
   statement (B1 verdict). Paid receiver-local bids were then added (B2).
5. **E1b as an instantiation of the Gaussian pair theorem.** The channels differ. Separated.
6. **"More revision rights make learning harder."** Recast as a strategy result.
7. **Exact enumeration of F_R in traffic.** Replaced by a declared candidate family.
8. **Topology generalisation (4×4).** The current fixed-width MLPs cannot run at a different m.
   Held-out LOADS are tested instead. A size-agnostic architecture would be needed; it is not
   built.

9. **"Bounded repair R1 beats a well-tuned direct selector" in traffic.** Development data says
   the opposite (§3.4). The supported traffic statement is about the charged bid for a direct
   budget-conditioned selector. Narrowed, 23:50.
10. **"η bridge closed" / "63% certified zero price".** Withdrawn. It is a one-swap local
    diagnostic (§5 table).

Nothing on the critical path was dropped silently. Steps 2, 5 and 6 are NOT DONE, not dropped.
CityFlow itself is not dropped. No result forces it.

## What still blocks a submittable MARL paper (in order)

1. **B4 closed-loop result** (running). Without a closed-loop win on fresh seeds, the method claim
   stays "held-phase only".
2. **Step 2: a learned communication-aware actor**, frozen for comparisons. Waits for B4 by the
   user's instruction.
3. **Strong comparators.**
   - Done (development): the independently trained direct selector.
   - Missing: LEARNED SchedNet / Where2comm adaptations with the same information and bytes. The
     current ones are heuristics.
4. **End-to-end latency.**
   - Missing: uplink/network delay acting on traffic, and a clean-machine latency re-measure.
   - fig3 Pareto exists as a working version.
5. **Learned-MARL runs** (5 training seeds, fixed/bursty/shifted, held-out load) and the traffic
   acquisition ablation.
6. **The manuscript.**
