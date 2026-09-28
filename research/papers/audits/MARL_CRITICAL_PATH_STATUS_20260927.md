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

## Update 28/09, 09:15 (the previous version is in legacy/MARL_CRITICAL_PATH_STATUS_20260927_v0010.md)

**Step 2 (learned communication-aware actor): ❌ → 🟡.**
- **Code.**
  - Actor side: `models/marl_comm_actor.py`, with the adapter (mask, age, fresh, heard, static
    topology; missing differs from zero), a shared actor and a centralised critic.
  - Trainers: `MARL_e3_actor_train.py` (MAPPO from scratch) and `_v2.py` (BC from MP2, then
    MAPPO).
  - Checks and evaluation: `MARL_e3_message_use.py`, `MARL_e3_continuation_labels.py` (the
    declared-continuation target), `MARL_e3_selector_train.py`, `MARL_e3_closed_loop.py` (+ v2 with
    cap, load and capacity shift).
  - Runners: `RUN_marl_e3_long*.sh`, resume and watchdog.
- **Protocols (written first).** `PROTOCOL_E3_PILOT_20260928.md` and
  `PROTOCOL_E3_SCRATCH_20260928.md`.
- **Development results so far** (`E3_INTERIM_RESULTS_20260928.md`).
  - Every finished learned actor beats MP2: select −15% to −24%, and on development MP2 is 12–23%
    worse (CI > 0).
  - G1 message use:
    - scratch s3 PASS (none +7.3%, shuffle +5.1%);
    - BC s3 PASS;
    - **BC pilot s0 FAIL**, so that chain's selector results are not read as a method result.
- **Blocked at 09:15.** The E3 processes deadlocked inside CityFlow's thread barrier around
  01:00–03:18. Stopping them needs the user (`pkill -9 -f "scripts/MARL_e3_"`). The resume runners
  with the watchdog are ready.

**Step 3.4 comparators.**
- The learned SchedNet adaptation exists (`MARL_e3_schednet_train.py`; v2 uses genuinely 1-byte
  weights).
- v1, with float weights: +1.1% and +1.9% against the prefix. It does not beat the committed
  cached-queue order.

**Step 5.**
- The frontier (caps +28/+56/+84/+140) and shift (headway 12; bursty capacities) runner and figure
  are ready: `RUN_marl_e3_frontier.sh`, `MARL_make_e3_frontier.py`.
- F4 mechanism figure: `figures_20260928_v4/fig4_mechanism_mp2`. Held-phase 18% of the oracle
  against 2–5% in closed loop; about a third of the edits harm; the target captures 49%.

**Step 6.**
- **Gates.**
  - `full9_20260928` VERIFY PASS: 301 modules, 2,382 theorems. It is the first full gate since
    full7, and MODS now holds every module the manuscripts cite.
  - `smokeOLD7b_20260928` SMOKE PASS: 251 modules, `imports_closed=1`, `native_decide=0`.
- **New Lean.** `LeanMarlE1bUniformV1` (the uniform shift halves the E1b constant without knowing
  the pair; readiness audit §5). smokeE1bU_20260928 SMOKE PASS; cited in paper_marl.
- **Paper.** `paper_marl.tex` has a learned-actor section with development numbers, F4, and TBD
  slots for the selector, frontier and shift.
- **One-command reproduction.**
  `SMOKE=1 bash scripts/RUN_marl_e3_long.sh <dir> 0` runs the whole E3 chain on tiny settings in
  about 2 minutes.

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

   The mechanism was therefore studied on one shared broadcast with heterogeneous receiver
   DECODING budgets (`PROTOCOL_HETERO_v0`). That protocol is named as a different model, as
   step 1.1 requires.
   - Corrected 23:56: nesting is NOT forced there.
     - `profile_cost` allows an explicit profile.
     - The env decodes exactly |S_i| = K_i payloads of the union; it does not model a receiver
       that listens to a time prefix and is cut off.
   - R0 is therefore the committed-order model. Direct selection is a legitimate comparator
     inside the same policy class, and measures the price of commitment.
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
- 🟡 B2 method latency is measured, COMPUTE ONLY.
  - **Idle** (`latency_b2_idle_20260928_000900`): median 14.8 ms, p95 16.1 ms, max 45.6 ms.
  - **Busy** (`latency_b2_20260927_232749`): median 16.6 ms, p95 17.9 ms, max 48 ms.
  - The two runs use the same seeds 601–604 and the same 208 steps, so contention raised the
    median by about 12%.
  - No bid uplink round and no network delay are modelled, so 0% misses at 50 ms is not an
    end-to-end guarantee.
- The baselines' latency is not measured.

**3.7 Delay consuming simulation time.** ❌ Zero delivery delay only.

**Done criterion** ("paired pilot showing repair useful + its latency cost"). 🟡
- Held phase: yes (B2).
- **Closed loop: B3 FAIL.** −0.26% [−1.20%, +0.62%] against the control, while the oracle gets
  −14.5%.
  - CONSISTENT WITH distribution shift induced by the policy itself (corrected 23:56; it was
    "diagnosed as"):
    - parity holds to 5e-6;
    - the shadow run would edit at 13–16 of 16 steps, but the live selector stops editing.
  - A second hypothesis is still live: held-phase target mismatch. The labels hold the joint
    action fixed for H = 3, while the live loop re-senses, re-selects and re-acts.
  - Parity rules out some wiring errors. It does not prove a single cause.
- **Second fresh panel 1101–1116** (descriptive, not preregistered): the frozen B2 design gets
  −0.28% [−1.65, +1.18] against the prefix. It edits 1–3 of 26 steps, against 19 for the oracle
  (−14.4%). Same symptom as B3.
- **B4 (DAgger), preregistered test on 801–816: PASS** (`B4_DAGGER_RESULTS_20260928.md`).
  - Retrained bid against retrained ctrl: −1.49% [−2.75, −0.23].
  - Against the prefix: −0.68% [−2.87, +1.37], not significant.
  - Against the frozen B2 design: +0.10%.
  - Part of the pass comes from the retrained control drifting to +0.89% against the prefix.
  - The retrained selectors edit 16–21 of 26 steps, like the oracle (19.5), but realise about
    4.5% of its −15.0%.
- **Target diagnostic** (`TARGET_DIAG_RESULTS_20260928.md`; 16 development states; self-checks
  PASS).
  - The held-phase argmax matches the continuation argmax in 1 of 16 states.
  - It captures 49% of the one-step continuation headroom, and is worse than the prefix in 4.
  - The target mismatch is real. Estimation error is still the larger factor.
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
- **Pareto (quality against bytes and latency):** 🟡 fig3 v4 (`figures_20260928_v4/`), redrawn
  after the readiness audit's figure notes.
  - Two figures:
    - `fig3v4_panel1101`: panel 1101–1116, including the independently tuned direct selectors;
    - `fig3v4_b4test`: the B4 test panel.
  - Short legend names; notes and the latency table are in `.caption.txt`.
  - One operating point (+84); it is not a multi-budget frontier. A frontier needs at least 3 byte
    budgets on the same design.
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
  - fig3 🟡 (v4, fixed MP2, one operating point).
- **Manuscript:** 🟡 working draft `research/papers/_tex/paper_marl.tex` (compiles with tectonic).
  - Content: problem/protocol, methodology, theory citing gated modules only, experimental
    design, and preliminary fixed-MP2 results with their artifacts. Learned-actor results are TBD.
  - The venue template waits for the track to be confirmed.

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
   setting was moved to heterogeneous receiver decoding budgets. Nesting is not forced there
   either (explicit profiles are allowed); R0 is the committed-order model. Reframed.
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

1. **B4 closed-loop result: PASS, weak** (see above). The method claim on fixed MP2 is
   "held-phase benefit, marginal closed-loop benefit".
2. **Step 2: a learned communication-aware actor**, frozen for comparisons. Waits for B4 by the
   user's instruction.
3. **Strong comparators.**
   - Done (development): the independently trained direct selector.
   - Missing: LEARNED SchedNet / Where2comm adaptations with the same information and bytes. The
     current ones are heuristics.
4. **End-to-end latency.**
   - Missing: uplink/network delay acting on traffic. The clean-machine re-measure is done.
   - fig3 Pareto exists as a working version.
5. **Learned-MARL runs** (5 training seeds, fixed/bursty/shifted, held-out load) and the traffic
   acquisition ablation.
6. **The manuscript**: a working draft exists; it needs the track/template and the E3 results.

## Claim map (28/09, 00:10; readiness audit P0.3)

- **Status legend:**
  - LEAN: compiled, smoke-gated, standard axioms, hypotheses satisfiable;
  - NUM: self-checking artifact;
  - OPEN: not established;
  - WITHDRAWN.
- No claim below is a traffic guarantee unless the row says so.

| # | claim (as it may be stated) | theorem / assumptions | code | artifact | status |
|---|---|---|---|---|---|
| 1 | Deployable regret of a committed order with R revisions ≤ 2(δ+u)(d−R)₊ + 2ε + ν + ζ; the constants 2u and 2ε are sharp | `LeanMarlEstimatedRevisionV1`; ScoreLocal(δ), score error u, estimation ε, search ν, coverage ζ | — | smokeMARL17 | LEAN (abstract). Traffic instantiation OPEN (row 12) |
| 2 | Per-receiver block frontier 2η Σ_i (d_i − R)₊ | `LeanMarlBlockFrontierV1`; needs hTop (prefix = top-score of the same vector) and ScoreLocal | — | smokeMARL4 | LEAN. In traffic, hTop is not checked: the runtime order is cached-queue |
| 3 | Zero commitment price under a 2δ cut margin; sharp constant | `LeanMarlRevisionFrontierV1`, `LeanMarlSubsetFrontierV1` | — | smokeMARL17 | LEAN |
| 4 | Nesting degree grows linearly: ≥ ⌊(m+1)/4⌋ | `LeanMarlNestingDegreeGeneralV1` (`nesting_degree_lower`, `distance_regret_lower`) | P1_d6_frontier search | smokeMARL17 | LEAN lower bound; equality is a CONJECTURE (m ≤ 8) |
| 5 | Exact non-nested team game: randomised price p(1−2p), deterministic min(p, ½−p), one revision closes it | `LeanMarlXorGameV1` | — | smokeMARL17 | LEAN |
| 6 | Calibration of ambiguous repairs on one Gaussian query channel: lower bound, constructive upper bound, pair version | `LeanMarlRepairCalibrationV1`, `LeanMarlCalibrationGapV1`, `LeanMarlPairCalibrationV1` | `MARL_E1a_two_stage_v2.py` | smokeMARL17 / smokeMARL4; E1 results | LEAN for the needle class. NUM: E1a measured cost lies between the bounds |
| 7 | E1b executable task: R = 2 is worse than R = 1 until about 25k rollouts, then better | a strategy result on the E1b channel (not the Gaussian channel) | E1b scripts | `E1_CONTROLLED_RESULTS_20260927.md`, figures v2 | NUM. Targeted ≡ uniform is a negative control |
| 8 | Under PROTOCOL_v1, tabulation is as fast as a prefix (the latency premise is refuted) | `LeanMarlTabulationV1` | latency premise check | LATENCY_PREMISE_CHECK | LEAN + NUM. The "priority is faster" claim is WITHDRAWN |
| 9 | Heterogeneous decoding budgets: the oracle R = 1 recovers 88% of the private gap | exact oracle over F_R (preregistered) | `HETERO_EXACT` producer | `HETERO_EXACT_RESULTS_20260927.md` | NUM (oracle) |
| 10 | A charged 1 B receiver bid improves held-phase selection for a direct selector, fixed MP2 | preregistered B2 | `MARL_hetero_b2_confirm_v2.py` | `B2_CONFIRMATION_RESULTS` | NUM PASS: +1.85 [+0.95, +2.84], 18% of the oracle |
| 11 | Closed-loop benefit on fixed MP2 | preregistered B3/B4 | closed_loop_v2 | B3 (FAIL), `B4_DAGGER_RESULTS_20260928.md` (PASS against the retrained control: −1.49% [−2.75, −0.23]) | NUM. Weak: −0.68% against the prefix (n.s.); no gain over the frozen design; about 4.5% of the oracle |
| 12 | T1 → traffic bridge (η) | would need an UPPER bound on one consistent score vector | `MARL_hetero_eta_bridge.py` | `eta_bridge_20260927.relabelled.json` | OPEN. The one-swap diagnostic is a lower bound only; the "certified" wording is WITHDRAWN |
| 13 | Bounded repair R1 beats direct selection | — | direct_indep | `BASELINES_DIRECT_STAGEA2_RESULTS` §2 | WITHDRAWN (development: direct ≥ R1) |
| 14 | Beats SchedNet / Where2comm | — | closed_loop_v3/v4 heuristics | same doc §1 | WITHDRAWN. Only heuristics exist; learned baselines are OPEN (E3) |
| 15 | Learned communication-aware MARL actor | — | none | none | OPEN (E3) |
