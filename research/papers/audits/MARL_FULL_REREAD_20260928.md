# MARL full reread and rescue search — started 28/09/2026 19:50 EDT

Request (author, 19:5x): audit EVERYTHING related to MARL so far, literally reread it; then reread the 10 earlier papers
(paper_a, paper_b, paper_c, adaptive, d6, functional, master, query, structural, support; unified skimmed); find what
can rescue the current situation (the E3 selector shows no incremental benefit over the same actor + prefix).

Method: read every MARL document in chronological order (research/papers/audits/MARL_*, PAPER_C_*, research/marl_budget/*.md),
the manuscript paper_marl.tex, the MARL models/envs/scripts and Lean modules, then the ten papers. Notes are appended
below per block as they are read, so nothing depends on memory. Each note: what the source says, whether it still
holds, and any lead for a rescue. Findings that are bugs or claim errors are marked FINDING; leads are marked LEAD.

## Notes

### Block 1 — 26/09 origin documents (Paper C reviews, trained-traffic plan, MARL synthesis proposal)
- PAPER_C_FINAL_NOVELTY_REVIEW: C = minimax signed-prefix regret of ONE permutation law under item bands for all budgets k;
  exact parity frontiers, value of budget information A = V − B, V^(1) = B (one exchange recovers the budget-aware value)
  on the four-item and even g_m families, robust-ball floor. Closest priors: Storandt–Funke (regret-min permutations),
  Singh–Kempe–Joachims (marginal constraints), recoverable selection (Chassein et al.), incremental maximisation.
- PAPER_C_PRACTICAL_TRAFFIC: proposes telemetry (net accumulation) with signed sensor contributions; warns the even family
  has sum g = 0 so an unrestricted estimator outputs 0 for free; requires a re-fitted-predictor baseline.
  Bridge: |L_K(S) − |Σg|/2| ≤ E_k, advantage A transfers if ideal A > 4E (derived, not Lean).
- PAPER_C_TRAINED_TRAFFIC_PLAN: C as NESTED MODEL COMPRESSION (METR-LA/PEMS-BAY, additive-branch CNN); the empirical
  object is a calibration cost table c(S) over all subsets; selected-policy transfer bound 4ε + ζ; mask bank must be a
  comparator. Never executed (the project moved to MARL on 26/09 23:02).
- MARL_SYNTHESIS_PROPOSAL (26/09 23:02): the ORIGINAL MARL question is the PRICE OF COMMITMENT when the budget is not
  known at commitment time, versus budget-aware selection, and how much a bounded pre-transmission revision recovers
  (T1); T2 compression certificate → control loss via performance difference (2e_T + 2ξ + ν)/(1−γ), with the
  distribution-shift caveat (occupancy of the COMPRESSED policy); T3 dynamic execution. Exact XOR three-message game:
  best singleton {1}, best pair {2,3}, V = p(1 − 2p), one replacement closes it.
  Step 3 of its progression: "train a common policy on sampled budgets; ... compare against direct subset selection
  conditioned on the revealed budget". Step 5: "fine-tune the policy and selector together".
  Stop rule (step 8): "If a simple budget-conditioned selector matches the method ... the recourse algorithm is not
  yet justified. If universal ranking loses no quality on traffic, report the negative result."
- LEAD L1 (structural): the E3 actor was trained ONLY under the committed prefix (R = 0), so every edit moves the actor
  off its training distribution of message profiles; the proposal's own T2 warns that the bound needs the COMPRESSED
  (edited) policy's occupancy. The mix actor was the one attempt to fix this and failed G1 (messages unused).
  Rescue direction to check later: co-training / budget-sampled training (step 3/5 of the original plan) was never run
  as specified — the mix actor sampled random +84 candidates, not the selector's own edits.
- LEAD L2 (question drift): the original question is commitment price under an UNKNOWN budget. E3 fixes the allowance
  (+84) and asks selector vs prefix at a KNOWN budget. The C-type quantity (value of knowing the budget; V^(0) vs V^(1)
  vs B across caps) has not been measured on the learned actor; the frontier runs (+28/+56/+84/+140) are the raw
  material for it. To check: do the frontier results show a budget-dependent best profile (non-nestedness) that a
  single committed order cannot follow?

### Block 2 — 27/09 morning (prior-art recourse memo, HANDOFF_a1b4, PROTOCOL v0/v1, ONE_PAPER plan)
- PRIOR_ART_RECOURSE: universal order (unknown-capacity knapsack, incremental submodular), recoverable selection,
  commitment-under-deletion, goal-oriented comms all prior. Warns: "R ít không đồng nghĩa latency thấp" — a direct
  budget-conditioned net is a MANDATORY comparator; if it dominates, drop the recourse-method claim. Error bridge
  ell(S_hat) − ell*_k ≤ g_R + 2ε + ν. Proposed surface V(N, R): N paid interaction observations (A), R repairs (C).
- PROTOCOL v0 §7b first oracle diagnostic (one-hop, max-pressure): 82% of states in the 2δ zero-price regime; the
  score-priority price is positive in 4.7% and R = 1 removes it; nesting price ~absent (0.17%). v1 §3 corrected the
  "m ≥ 7" overstatement. v1 main contract: ONE network-wide packet budget k_t, broadcast, public scheduler.
- ONE_PAPER plan (27/09 12:56), title "When Is a Communication Priority Enough?". Two-hop max-pressure diagnostic:
  score order gap 17.5% of tables at R = 0, 3.25% at R = 1; best nested order gap 0.71% at R = 0, 0 at R = 1.
  Algorithm "Learn–Check–Revise": train communication-aware actors by CTDE WITH RANDOM MASKING OVER THE BUDGET RANGE
  (§9 first bullet), freeze, fit evaluator, repair only when the certificate fails.
  §11 fallback: "If learned traffic still has no nesting price, the main result can be the CONDITION under which one
  priority suffices and its data-efficient learning, with repair as exception handling." "If a direct conditioned head
  dominates ... stop claiming a strong MARL method paper."
  §13 joint A+B+C packet game (M0 noisy copy, XOR shares on 3 edges, one bad edge): V_det = min{a, h−a},
  V_rand = a(h−a)/h, V^(1) = 0; common repair before identification (B); optimized-starvation Γ_f > 0 (A);
  E τ ≥ kl/(β K(h)). exact_check.py: 1,209 assertions.
- LEAD L3 (the question the title asks has an answer in our data): E3 says that, for learned actors at +84 B, NO legal
  selector beats the committed prefix, although the in-family oracle has +15 (H = 3) headroom. That is exactly the
  ONE_PAPER §11 branch "a priority suffices" PLUS a measured information gap (the oracle headroom is not learnable from
  legal inputs). The F5/F5b decomposition (coverage / geometry / selection regret, ranking loss vs threshold) is the
  quantitative form of "cost of knowing what to repair" (§7.3/§13.5). This is a scope/framing lead, which is the
  authors' decision (FINISH_HANDOFF: changing scope is not the worker's call). Record, do not act.
- LEAD L4 (never executed as planned): §9 says train actors with random masking over budgets; WP5.4 end-to-end track.
  E3 trained actors only with R = 0 prefixes (scratch) or MP2-BC then prefix PPO (BC); the mix actor used random +84
  candidates. A budget-sampled (varying k) actor was never trained. Check later whether this is the budget-conditioned
  direct comparator's natural home.

### Block 3 — 27/09 midday (FINAL_SCOPE, QUICKFIX manifest, SUBMISSION_CRITICAL_PATH, cheap checks README, CHEAP_V2 audit)
- FINAL_SCOPE title "Learning When to Revise Communication Priorities in Budgeted MARL"; stop rules: if a direct
  budget-conditioned selector is ≥ on all axes, no practical-advantage claim; "Best ranking good but score ranking bad:
  the empirical contribution is learning/repairing the score, not 'every priority fails'".
- SUBMISSION_CRITICAL_PATH step 2.2: "Train with the declared budget/mask diversity so the actor learns to USE messages
  and TOLERATE missingness" — again the actor is meant to be trained on diverse message sets.
  T1 (LeanMarlEstimatedRevisionV1.deployed_regret + RevisionAuditBridge feasibility); T2 LeanMarlRepairCalibrationV1
  (Gaussian needle, finite horizon, known gains). "The heaviest missing piece is learned-MARL evidence and a benefit
  over a direct budget-conditioned selector."
- CHEAP_V2 audit (MP2 actor): no latency, unseen-budget, or learned-quality advantage for prepared priority + revision
  under PROTOCOL v1 → those claims RETIRED for v1. The heterogeneous (+4.81 private vs shared) number is a best-found
  heuristic difference, not a bounded-revision result. "Fresh bids" were NOT charged in v2 (offline ablation). The
  'ceiling' is privileged current summaries, not full state. Full comm < none for MP2 (5.46): a FIXED decoder can lose
  from more information.
- Old pilot (CHEAP_V2_RESULTS): held-out test regret, public features: prefix 24.45, critic chain 25.65, direct net
  (expected-gain softmax loss) 23.43 — the only learned method below the heuristic, 2 traffic-seed IDs, no CI. Train
  regret 4.7–8: a large generalisation gap already on 27/09, with MP2 (no learned actor).
- LEAD L5 (history repeating): the E3 finding "critic fits train (0.65 pair acc) and is at chance on DEV" is the SAME
  generalisation gap first seen on 27/09 (train regret ~4.7 vs test ~25.7 for the critic). Six rounds of selector
  variants since then (v2 head, v3 privileged, v4 queue bid, v5 multi-class, acquisition, dense labels) attacked
  inputs/labels, never the train→held-out gap mechanism itself. The one method that beat the heuristic held-out in
  2 seeds was the expected-gain DIRECT net — i.e. the DFL objective now proposed in v6. This makes the DFL test a
  replication of the only positive held-out signal the project ever had, and argues for running it.

### Block 4 — 27/09 afternoon (CHEAP_V2 results, LATENCY premise, HETERO exact, HETERO step-3 decision, SCOPE after cheap tests)
- LATENCY_PREMISE: with k known at the same moment, a per-budget TABLE dominates prefix + revision in value and latency
  (LeanMarlTabulationV1: tabulated regret ≤ 2ε + ν, no geometric term). Revision is only justified where nesting is
  physically forced (one stream, heterogeneous receivers) or by sample-efficiency. Global-budget screen (MP2): the loss
  comes from the SCORE, not nesting (cached-queue prefix regret 23.1; its oracle R1 4.09; best nested chain 0.33).
  Pilot: learned repair WORSE than its own prefix on train and test ("exactly the 2ε term of T1").
- HETERO_EXACT (MP2, certified by enumeration): advance order + one patch per receiver +8.45 over R0 (16/16 episodes),
  recovers 88% of the private gap; heuristic order + 1 patch +27.2 (89% of private). Bytes +16–26 per step.
  "private beats exact known-budget best shared in 106/256" — the heterogeneous mechanism is REAL for an oracle.
- HETERO step-3 pilot (MP2, test seeds 61–64, cap +28): oracle R1 +16.6; public learned R1 +0.89; direct local search
  +0.94; privileged summaries −0.43. "The tested search CAN reach good solutions with the true evaluator; the learned
  evaluator does not choose them." Same pattern as E3 now (oracle +15, learned ≈ 0).
- SCOPE_AFTER_CHEAP §3: "Test a paired gain target, RANKING/DECISION LOSS and regularised or structured predictors on
  the EXISTING labels before collecting a large new dataset." Stop rule: if that diagnostic fails, stop expanding the
  learned-traffic direction; "do not automatically add fresh bids, a larger actor or a new simulator."
  Also FINDING (historical, 27/09): the public feature vector omitted the receiver-specific delivery history (receivers
  hold different old versions of a sender's packet); fixed later by the scheduler mirror (cityflow_hetero_mirror.py).
- LEAD L6: a DECISION/RANKING loss was recommended on 27/09 18:27 on existing labels; to verify in the next block
  whether it was ever run for the hetero selector (MP2) — if it was not, v6 DFL is the first test of the 27/09
  recommendation, and the old MP2 hetero labels (hetero_pilot_20260927_181207) are a second, independent data set on
  which the same DFL arm can be run offline at zero rollout cost (different actor: MP2, so descriptive only).

### Block 5 — 27/09 evening (HETERO pilot results, diagnostic audit, diagnostic v1/v2)
- MP2 hetero pilot: learned critic captures ~5% of the oracle R1 headroom; critics memorise (train regret 0.6–1.5,
  three of six selected checkpoints at epoch 0).
- Diagnostic v2 (anchored scores, prefix-favouring ties, inner-selected τ incl. never-edit), validation 51–52, +28 B,
  oracle +14.59: every LEGAL learner ≈ 0 (best mlp_history +0.78 one seed); PRIVILEGED JOINT ACTIONS ALONE
  (the actors' actions under the candidate and under the prefix) recover +7.1…+8.0 (~half), 3–4/4 episodes,
  concentrated at headway 8. Current summaries alone do not help. ~60% of non-prefix candidates have EXACTLY zero
  gain and ~59% induce the SAME joint action as the prefix; for legal MLPs only 27% of "edits" change the executed
  action. Decision then: stop learned-traffic expansion (later overridden: B1–B6, E1, E3 were run).
- LEAD L7 (information-structure rescue, to test): the missing information is the actors' RESPONSE to a profile.
  A receiver's action changes only if a delivered payload DIFFERS from the stale copy it would otherwise use AND the
  receiver's policy is sensitive to that difference. The first factor is known to the SENDER (its fresh measurement
  vs the version the scheduler mirror says receiver i holds); the second to the RECEIVER (its logit gap / local
  sensitivity). Tested so far: receiver-side bids only (top-2 logit gap = "response bid"; own queue total = "queue
  bid"). A SENDER-SIDE INNOVATION signal (|fresh_j − cached_ij| per receiver, the event-triggered / value-of-
  information quantity) has, as far as read so far, never been offered to the selector. It is legal (sender's own
  data + the public delivery history), cheap (1 B per sender), and directly targets the ~60% zero-gain /
  ~59% same-action candidates. Prior art: event-triggered communication (ETCNet), value/age of information — so it
  is a method repair, not a novelty claim. Verify in later blocks (B2 fresh bid, E3 bids) that it was not tried.

### Block 6 — 27/09 night (STORY_VERDICT, B1 protocol/verdict/results, B2 protocol, mitigation dev, B2 confirmation)
- STORY_VERDICT: the reframe "price of NESTING"; one-hop global-budget oracle: 82% of tables in the 2δ zero-price
  regime; nesting degree ≤ 1 for m ≤ 6 (Lean + enumeration). Update 3: loss comes from the SCORE, not nesting.
- B1 (MP2, 8× data, preregistered): FAIL. Legal selectors 1–5% of oracle and FLAT in N (8→64 seeds); privileged joint
  actions 62–66% already at N = 8. "Increasing data did not close the gap for these learner/representation/selection
  choices." Public MLP small positive CI (+0.62 [+0.01, +1.29]).
- Mitigation dev (MP2): legal response model near chance (action acc 0.103 vs chance 0.125; change precision 0.29,
  recall 0.09); RECEIVER-LOCAL info IS informative (local preferred action = true prefix action 67%; local gap predicts
  change 0.30 vs 0.10 by quintile). A classification decision loss `cls_history` (BCE on 1[gain > 0]) was tried:
  +0.03…+0.53 over control, all CIs contain 0 — so a (pointwise) decision loss was already tested on MP2 without a clear
  signal; the LISTWISE expected-gain loss of v6 was not (it was used only in the 27/09 global-budget cheap pilot,
  where it was the best held-out learned method). `struct_legal` (the scheduler runs the KNOWN MP2 code on
  mirror data): +0.4…+0.7 legal gain, CI > 0 at +28.
- B2 confirmation (fresh seeds 601–616, preregistered, frozen): PASS. mlp_top2_joint (1 B receiver bid, stage-A
  response model trained on privileged labels, critic on predicted soft joint action), direct, +84: Δ vs ctrl_history
  +1.85 [+0.95, +2.84]; own gain +3.12 [+1.70, +4.59]; all 3 seeds > 0; beats same-byte queue bid (+0.98). 17.7% of
  oracle. THIS IS THE ONLY CONFIRMED POSITIVE LEGAL SELECTOR RESULT IN THE PROJECT (MP2 actor, offline H = 3).
- LEAD L8 (what made B2 work, and whether E3 ported it faithfully): the B2 winner is a TWO-STAGE model: (A) predict
  each receiver's response (soft joint action) from the 1 B bid + scheduler-side refresh score; (B) critic on the
  predicted soft joint action. E3's "response head" (sel_bid_resp) appends per-receiver change PROBABILITIES to the
  candidate features of the same MSE critic; its dev recall is 0.15 (precision 0.53, base rate 0.11, accuracy 0.8955
  vs always-no-change 0.8936) — i.e. the E3 head predicts almost no changes. Check in the E3 block: (i) whether E3 has
  a structural response model (the learned actor's own network run on scheduler-reconstructable views = the analogue
  of struct_legal, which is legal because the actor weights are public), and (ii) whether the E3 head predicts the
  soft joint action (as B2 did) or only a change bit.

### Block 7 — 27/09 late night (B3, B4, B5/B6, target diagnostic, direct baselines / stage A v2)
- B3 (closed loop, frozen B2): FAIL. −0.26% [−1.20, +0.62] vs control; the model stops editing after t ≈ 5 (edits
  2.15/26 steps vs oracle 19.2); shadow mode on the prefix trajectory would edit 13–16/16 → "consistent with
  policy-induced distribution shift" (not proved).
- B4 (one DAgger iteration): registered PASS vs retrained control (−1.49% [−2.75, −0.23]) but vs PREFIX −0.68% n.s.;
  the control got worse (+0.89%); the retrained selector edits as often as the oracle (20.6 vs 19.5) but realises
  4.5% of the oracle's −15.0%. "The editing symptom is fixed, the benefit is not."
- CLOSED-LOOP ORACLE HEADROOM (MP2, held-phase greedy each step): −14.4% to −15.0% Σ waiting, 32/32 episodes,
  +8% finished trips. Real, large, repeatable.
- B5 struct_legal (legal only): FAIL c1 by a hair (Δ +1.02 [−0.04, +2.13]); own gain +1.36 [+0.16, +2.53].
- B6 robustness: the B2 bid advantage holds at other loads, NOT under fixed/bursty/low capacity processes; the
  privileged reference stays at 10–33 everywhere.
- TARGET_DIAG: held-phase labels vs cont_3 labels: the held-phase argmax equals the continuation argmax in 1/16 states;
  captures 49% of the continuation headroom; worse than prefix in 4/16. Hence E3 moved to cont_3 labels.
- DIRECT vs R1 (MP2, dev, independently tuned): direct beats R1 by +1.1…+1.6 (CI > 0) at +56/+84/none; ties at +28.
  "The supported statement is 'a charged receiver-local bid helps a budget-conditioned (direct) selector in the
  held phase'. It is NOT 'limited revision R beats direct selection'." SchedNet-style heuristic stream ordering by
  fresh own queue is WORSE (+4.7%).
- FINDING (still relevant): the η "bridge" was a one-swap LOWER bound, not a T1 certificate (corrected then). Same
  class of issue as the later F5 bridge correction.
- LEAD L9 (the real gap is 15% vs 0.7% in closed loop, and it is an ESTIMATION gap): MP2 shows three regimes:
  (a) oracle held-phase, per step, −15%; (b) best legal learned (bid + stage A), −0.3…−0.7%; (c) privileged joint
  actions offline recover 64–84%. So "knowing what the receivers will do" is worth most of the gap. For a LEARNED
  actor the receivers' decision function is a known network; the scheduler can in principle run it (struct_legal
  analogue). The limiting quantity is then only the fresh-payload uncertainty, which is exactly what the sender-side
  innovation signal (L7) addresses. Combination L7 + L8 = "sender innovation + receiver-side actor simulation"
  is the most direct attack on the measured bottleneck that has not been run.

### Block 8 — 27/09 night (E1 audit + results, critical-path recheck, publication readiness)
- E1: controlled calibration (E1a Gaussian needle matches T2; E1b executable Bayes-decoder task is a mean-structure
  extension only — its paired squared-loss rewards have interaction-dependent variance, so no KL bound transfers).
  "R2 worse than R1 until 25k" is an ALGORITHM result (F1 ⊂ F2), not an intrinsic cost.
- E1 audit §8: "predict actor responses using privileged action labels at TRAINING time and legal inputs at inference;
  a naive factorisation E[value | z, S] = Σ_a p(a | z, S) Q(z, a) can FAIL because hidden state affects both the
  selected action and the rollout value" — a caution for any two-stage response model (B2 stage A, L8).
- PUBLICATION_READINESS (27/09 23:53): TARGET VENUE = CCSC Eastern (faculty track, JCSC, anonymous review, 15 pages
  incl. references, CCSC template). "A focused, reproducible study with correct comparisons and a clear explanation is
  more useful than packing every theorem and simulator." §4.4: "nesting forced" is NOT unconditional with the current
  transport (explicit profiles are allowed, so direct selection is a legitimate competitor; receiver capacity = number
  of decoded payloads, not listening time). §5 decomposition V_all − f(Ŝ) = geometric + byte + coverage + estimation;
  and the information gap E[max f_X | Z,K] − max f̄_Z (privileged oracle vs conditional value).
  §6 sharpest question: "when receivers have different budgets, is coordination quality lost to commitment, to limited
  repair, or because the scheduler does not know how the actors will respond; what does a small paid bid buy back?"
  §8: "changing the claim type to analytical/empirical limits with CityFlow evidence" vs "dropping MARL" are two
  different decisions; the data force only lowering some claims; the choice is the user's/advisor's.
- LEAD L10 (venue fit): for CCSC Eastern, the §6 question already HAS a measured answer on two actor classes (MP2 and
  learned): commitment/structure is not where the loss is; the loss is the scheduler's ignorance of the receivers'
  response; a paid response bid buys back ~18% held-phase on MP2 but not closed-loop. That is an "empirical limits"
  paper with rigorous controls — a legitimate option that the authors must choose (not the worker).

### Block 9 — 27/09 23:56 → 28/09 16:54 (novelty check, HETERO v0, E3 protocols, finish handoff, status, post-F5,
### provenance, 16:11 recheck, seeds deviation)
- NOVELTY_CHECK (27/09 20:40): "The story is an ANALYSIS paper, not a methods paper." Finish line A (analysis, this
  cycle) vs B (learned MARL method, "not reachable this cycle"). The author then chose B (E3).
- HETERO v0 Amendment 1: capacity = number of DECODED payloads, exact cardinality, explicit profiles allowed →
  "nesting is NOT forced inside the policy class"; direct selection measures the price of commitment.
- E3 actor input (CommAdapter): own sensor, own phase, agent one-hot, per sender j: fresh, heard, age, payload
  (phase, elapsed, vehicles, waiting), topology. So an edit changes BOTH the flags/ages (known to the scheduler) AND
  the payload content (unknown to the scheduler).
- FINISH_HANDOFF F2.B asked for a response model predicting the phase / joint-action DISTRIBUTION (the binary head
  only predicts change) → done as selector v5 multi-class head: negative (DEV −1.1…+0.5). F2.C mix actor done: G1 FAIL.
  F2.A privileged joint action on E3 labels: priv arms up to +2.7 DEV (≈18% of oracle), much weaker than on MP2
  (50–66%). Reason (my reading): E3 labels are cont_3 (the candidate's effect on caches carries into t+1, t+2), so the
  first-step joint action no longer determines the value, unlike the held-phase MP2 labels where f_x(S) = Q_H(x, a_x(S)).
- POST_F5 recheck: F5 reduced bridge valid at η_top on 16/16 states; the scores are fitted post hoc (numerical
  instantiation, not a certificate).
- 16:11 recheck: N1 (best found = max of both searches: 20.75 / 16.29) and N2 (the "estimation" term includes the
  threshold/abstention rule; unthresholded critic argmax: scratch +0.19 mean, BC negative).
  Mix actor: stale +7.51% [5.66, 9.48] (old messages clearly hurt), none −0.90% (G1 FAIL), full −1.85% n.s.
- LEAD L11 (the mix actor's stale result): the mix actor, trained on random +84 candidates, IGNORES the absence of
  messages (none −0.9%) but is HURT by stale ones (+7.5%) — it learned to rely on the fresh/age flags. The scratch
  actors have none +4–9%. This means the actor's use of messages depends on the training profile distribution, and
  a selector's edits change exactly those flags. Supports L1/L4: any selector result is conditional on an actor that
  never saw non-prefix profiles; the one actor that did see them stopped depending on content.

### Block 10 — 28/09 (current claims, E3 interim log in full, self-audit ledger incl. the other session's L-59/L-60)
- E3 facts re-read: 95.8% of candidate values tie with another candidate in the same state; 34% (scratch) / 42% (BC)
  of candidates tie with the prefix exactly; continuation gains are integer waiting counts (coarse target).
  Response head: accuracy 0.895 vs always-no-change 0.894, recall 0.15 with the bid. Privileged-only arm ≈ 12–20% of
  oracle on E3 (MP2: 50–84%). Multi-class head F2-B negative. Every legal arm −2.34…−0.19 DEV.
  MP2 IMPROVES with delivery delay (−3% … −7%); the learned scratch actor degrades (+3.9% at 20 s, +5.6% at 30 s).
- NEW (other session, 19:3x–19:5x, ledger L-59/L-60, "recorded, not results"):
  L-59 EDGE-structured legal model (per-(receiver, sender) features: mirror, latest paid payload, CONTENT CHANGE
  between them, adjacency) → DEV one-swap pair acc 0.51–0.52, ~0.5–0.7 of 9.5 units (strict metric, little affected).
  L-60 EMULATION probe: the actor network run on the scheduler-reconstructable view reproduces the actor's action at
  chance (prefix action 0.16 / 0.11) — UNVERIFIED (reconstruction not validated; possible encoding bug).
  → The struct_legal analogue for E3 (L8) has been tried by the other session and failed (unverified). The legal
  "content change" in L-59 is stale-vs-latest-PAID, not the FRESH innovation of L7, which stays untested (it needs
  the sender's current measurement, i.e. a paid sender-side bid).
- SYNTHESIS so far (MP2 + E3, ~20 selector designs): the scheduler lacks exactly the two FRESH quantities that
  determine the actors' response — each receiver's own current sensor and each sender's current payload. Everything
  legal that does not carry fresh information (history, mirror, content change of paid packets, emulation on
  reconstructed views, additive/edge models, acquisition, dense labels, multi-class heads) ranks at chance.
  Designs that carry some fresh RECEIVER information (B2 top-2 bid on MP2) recover a fraction (18% held-phase).
  No design has carried fresh SENDER information into the choice.

### Block 11 — manuscript paper_marl.tex (read in full)
- Title "Committed Priorities, Bounded Revision, and Paid Bids for Budgeted Multi-Agent Communication"; the TODOPAR
  already states the method-scope condition is NOT met on development data.
- Fig. 1 caption: "A single swap for one receiver gains 31 units ... although NO ACTION CHANGES at the current step:
  the benefit arrives through what the receiver CACHES for later decisions" — the value of an edit is often a
  cache-refresh effect, i.e. a freshness/innovation effect (supports L7).
- Methodology states the Recipe-L critic receives only predicted CHANGE PROBABILITIES of the current action; nothing in
  the recipe represents the future-cache effect that Fig. 1 shows is where much of the value comes from.
- FINDING (manuscript, minor): §Theory Remark says "The last term is at most 2ε+ν (the argument of Theorem 1)" — true;
  §E3 later correctly says ν ≠ 0 for the deployed thresholded rule. Consistent. No new error found in the read.
- LEAD L12 (cache-effect representation): under cont_3 labels, an edit's value = (effect on the current joint action)
  + (effect on what receivers will hold at t+1, t+2). The second term depends on (i) how stale the receiver's current
  copy of sender j is (age — LEGAL, in the mirror), (ii) how much j's measurement has changed since (innovation —
  sender-fresh, not legal without a bid), and (iii) whether the prefix would refresh j at t+1 anyway (LEGAL: the
  committed order is known). A selector feature "would this delivery be redundant with next step's prefix?" is legal
  and cheap and was not in any recipe read so far (to confirm in the code block).

### Block 12 — code read: actor adapter, selector features, response head, label record, committed order
- Actor input per sender j: fresh flag, heard, age, payload (phase, elapsed, vehicles, waiting), topology.
- Label record: legal inputs (z, K, mirror, order, bid, b0) + per candidate (sets, bytes, cont, cont_1, joint).
  FRESH sender payloads are NOT stored (a sender-innovation test needs one deterministic replay per episode).
- Committed order = `cached_queue_ranking`: never-heard senders first, then by DESCENDING CACHED waiting; staleness
  is ignored, so a sender whose cached queue is low is rarely transmitted and its copy stays stale (a starvation loop,
  the literal traffic analogue of Paper A's "surrogate scores starve decision information").
- Critic features: z, K/m, mirror, bid, candidate m×m mask and edit mask, byte delta. Response head: added/dropped
  senders' summed mirror age, never-heard count, |latest paid − receiver cached| waiting, adjacency.
- QUICK READ-ONLY PROBE (scratchpad/age_probe.py, 28/09 ~20:15) to test L7/L12 before proposing them: score a candidate
  by the summed staleness of the senders it adds minus those it drops (legal). Tie-half pair accuracy:
  scratch s3 TRAIN 0.484 [0.473, 0.497], DEV 0.458; BC s3 TRAIN 0.468 [0.454, 0.481], DEV 0.437 — BELOW chance on
  768 train states: delivering STALER senders is on average WORSE. The fewer-edits rule: 0.509/0.529 and 0.522/0.557.
  → The naive age-of-information rescue (refresh stale senders; age-aware priority) is NOT supported on these actors.
  Plausible reading (not tested): prefix-trained actors are adapted to fresh data from high-queue senders; staler,
  low-queue senders' fresh data is out of their training distribution. L7 (true fresh innovation) is untouched by this
  probe (age is only a proxy for innovation) but its prior is lowered.

### Block 13 — MARL Lean modules (statement headers)
- SafeEdit, EstimatedRevision (T1), BlockFrontier, ProfileSearch, Tabulation, Starvation, ProxyBlindness,
  RevisionAuditBridge read at statement level.
- KEY: LeanMarlProxyBlindnessV1 ALREADY PROVES THE DICHOTOMY THE E3 DATA SHOW: two worlds agreeing on all
  first-order (size ≤ 1) information; an oracle with R = 1 has regret 0 in both ("enough POWER to repair"); every
  rule seeing only first-order information has worst-case regret ≥ 4, randomised too ("not enough INFORMATION to
  repair correctly"); ONE paid pair measurement makes regret 0. i.e. V(first-order, R=1) ≥ 4 > 0 = V(oracle, R=1).
  E3: the in-family oracle with a few swaps captures +15…+21 (power suffices); every legal rule ≈ 0 (information
  does not); privileged response information recovers part (a paid measurement of the right thing helps).
- LEAD L14 (theory already matches the negative data): the manuscript currently leads with T1 geometry, which F5/F5b
  show is NOT where the loss is. ProxyBlindness + Starvation + T2 (calibration of ambiguous repairs) are the theorems
  whose SHAPE matches the traffic evidence: structural sufficiency with information insufficiency, and a price for
  the information that resolves it. A re-weighting of the theory section around them needs no new theorem; turning
  the E3 information contract into an instance of ProxyBlindness (two traffic states with identical legal inputs and
  different optimal repairs) is a concrete, checkable empirical object (see Block 15 rescue list).

### Block 14 — the ten earlier papers (abstracts + results sections; A, B, C, adaptive, d6, functional, master, query,
### structural, support; unified skimmed)
- A: surrogate-optimal designs STARVE the cells that carry the decision; repair = sacrifice β of surrogate value,
  exact exchange rate 1/(8rM); budget law for adaptive policies; the surrogate-tracking learner pays an extra log.
- B: deciding needs less than identifying; obstruction = set of worlds with no common safe answer; the ADMISSIBLE
  QUERY menu fixes the information order; choosing a menu to reach an order is NP-hard (hitting set).
- C: one committed order for all budgets; value of budget information; one exchange recovers it on stated families.
- adaptive: tracking/apportionment deficits (not relevant to the rescue).
- d6: 2δ margin is the sharp threshold for Top-C optimality (T1's origin).
- functional: a proxy computed at FROZEN current extrema (ordering constraints dropped) is wrong in both directions
  when extrema can MOVE; the true alternative set must let the extrema move.
- MASTER: NECESSITY DICHOTOMY — when an instrument sees the quantity only with an unknown offset, there are
  configurations where every ordinary query has identical means in two worlds whose answers differ: value EXACTLY
  ZERO, no amount of ordinary sampling recovers it; admitting a CALIBRATION query (price κ) gives the exact law
  Γ* = Δ²/(2K(√(vm)+√(νκ))²); uniform allocation then reaches 73.5–100% of optimum — the query TYPE matters, not the
  allocation.
- query: the leakage order is a property of the ADMISSIBLE MEASUREMENT, not of the worlds; a factor 8.8 in samples
  attributable entirely to which measurement is legal.
- structural: a MENU of a few schedules can serve all budgets where one cannot (five rankings necessary below a
  tolerance); ex-ante vs ex-post (V_path/V_avg = m − 1).
- support: name a safe tip without identifying the world; decide risk independent of K, identification grows.
- unified: certifying a margin costs more than making the decision; common safe answer ⇔ no obstruction inside a
  class; the cheap single-swap surrogate of the geometry term is UNSOUND (same lesson as the η one-swap bridge).
- LEAD L15 (MASTER is the template for the E3 negative result): the E3 scheduler sees each sender's queue only
  through a STALE copy — the quantity plus an unknown drift since the last paid packet, an offset in MASTER's sense.
  MASTER predicts exactly what E3 found: ordinary (legal) information can have value ≈ 0 for the decision, and the fix
  is a different QUERY TYPE (a calibration query that measures the offset), after which even a naive allocation is
  near-optimal. The E3 bids measured the RECEIVER's preference (top-2 logits), not the SENDER's drift; the same-byte
  queue bid measured the receiver's own queue. The MASTER-type calibration query for E3 is the sender's drift since
  its last paid packet — L7. MASTER also supplies the form of a price law (square-root combination of the two query
  prices) that a paid-drift protocol could be analysed with.
- LEAD L16 (Structural menu as a regulariser): replace "edit the prefix among ~180 candidates" by "choose one of a
  small MENU of committed orders" (e.g. cached-queue, age-weighted, least-recently-sent, cached-queue with forced
  refresh). Fewer options = smaller optimizer's curse (the R1-as-regulariser effect seen on MP2 and E3), and labelling
  K menu prefixes per state costs K/180 of the current labels, so the same rollout budget buys ~40× more states
  (attacks the data-scale side too). Theory: Structural's menu results; C's commitment. Untested; oracle headroom of a
  small menu unknown (must be measured first, from new labels).

### CORRECTIONS 20:12 (independent reviewer, forwarded by the author) — these notes overstated four points
- "Privileged recovers ~12–20% of the oracle, so a low ceiling" (Blocks 9–10, L9): WRONG INFERENCE. That is the score
  of one TRAINED privileged evaluator, not a ceiling of every method that has the information; the privileged
  evaluator can itself learn badly.
- "B1 on MP2 predicts that more data is useless for the learned actor" (Blocks 6, 10): only a reason for caution.
  Actor, target and data differ; B1 must not pre-empt F1.
- "The mix actor was negative, so co-training is not worth it" (L1, L11): NOT TESTED. MARL_e3_actor_train_mix.py:65
  draws RANDOM profiles; no scheduler was trained jointly with the actor. L1/L11 stand only as "any selector result is
  conditional on a prefix-trained actor"; nothing is concluded about co-training.
- "The probes confirmed the information sits at the receiver / the scheduler lacks exactly the fresh quantities"
  (Block 10 SYNTHESIS, L-60 reading in Block 13/L-64): NOT ESTABLISHED. L-59 used the strict metric; L-60's
  reconstruction was never validated against true views, so an encoding error is not excluded; the ledger itself says
  neither may be cited as a result. The staleness probe (Block 12) is one legal proxy, not a test of the fresh
  information hypothesis.
- Current wording, as in E3_INTERIM (18:57): out-of-sample ranking ability is weak; THE CAUSE IS NOT ISOLATED.
  Information, the learning objective, data scale, label noise and representation all remain live explanations; the
  DFL round tests only the objective.
- MP2 is not "missing a closed loop": B4 ran it (−0.68% vs prefix, CI contains 0). The MP2 problem is the lack of a
  convincing benefit, not a missing test.

## Synthesis (20:15, after the corrections above) — what could rescue the method goal, ranked by evidence and cost

Status: the method-scope condition is NOT met on development data; the cause of the weak out-of-sample ranking is NOT
isolated. The author's direction (20:1x) fixes the order: one controlled DFL round now, finish F1 and the multi-actor
panel, read them together, open nothing else.

| # | option | prior evidence | cost | status |
|---|---|---|---|---|
| 1 | DFL objective (Amendment 1: MSE-all / MSE-feasible / DFL, T = 1, equal lr grid) | the only held-out learned win in the project: 27/09 MP2 cheap pilot direct net (2 seeds, no CI); a pointwise decision loss (cls_history) on MP2 was n.s. | 27 fits/actor, offline | RUNNING NEXT (scratch s3, then BC s3 secondary) |
| 2 | F1 dense labels (registered) + 5-actor scratch panel | B1 on MP2 is a caution only (different actor/target/data) | running | finish; audit labels; read with 1 |
| 3 | byte saving at non-inferiority (author's preferred fallback) | 34–42% of candidates tie the prefix exactly; this does NOT show that dropping transmissions keeps quality (needs a real drop protocol, correct cache update, closed loop) | new protocol + small pilot, margin pre-set | only after 1–2 are read negative |
| 4 | a small MENU of committed orders (Structural) instead of ~180 edits | none measured; oracle headroom of a menu unknown | new, cheap labels (K per state) | idea only; not opened (author: no new branches) |
| 5 | sender-side drift bid (MASTER-type calibration query) | MASTER's dichotomy has the matching shape; the legal staleness proxy was below chance | replay per episode + offline fits | idea only; not opened |
| 6 | receiver-computed sensitivity bid | B2 (receiver-local, MP2) is the only confirmed legal positive; L-60 unverified | medium | idea only; not opened |
| 7 | actor–scheduler co-training | NOT tested (the mix actor used random profiles) | high | not opened |
| 8 | scope change (analysis / empirical limits; ProxyBlindness + MASTER + T2 shape) | theory already matches "power suffices, information/learning does not" | writing | the AUTHORS' decision, not the worker's |

What the reread found that is new relative to the claim map:
- The in-repo precedent of the DFL loss (MARL_cheap_checks_v2_train.py) and its held-out result.
- LeanMarlProxyBlindnessV1 and MASTER's necessity dichotomy are the theory whose shape matches the E3 negative result;
  the manuscript leads with T1 geometry, which F5/F5b show is a small part of the loss.
- The committed cached-queue order ignores staleness (a starvation loop in Paper A's sense), but delivering staler
  senders is on average worse for these prefix-trained actors (probe, Block 12).
- The venue context (CCSC Eastern faculty track, 15 pages) favours a focused, reproducible study with honest
  comparisons (PUBLICATION_READINESS §2).
