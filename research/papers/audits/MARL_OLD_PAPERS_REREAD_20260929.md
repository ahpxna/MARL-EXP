# The ten papers re-read together, against the MARL/E3 problem list (29/09/2026, started 19:4x EDT)

User request (19:3x): dig through every result and artifact (the MARL ones and old papers' where a formula or lesson
bears on MARL); check consistency; propose a list of where the problems can be; then re-read all old papers together and
research and validate solutions.  Evidence ids are the MARL ledger's (L-…).  Reading notes per paper, then the problem
list and the solution map at the end.

## Paper A (paper_a.tex, read in full): the price of a frozen surrogate
Object:
- a compression decision with moving extrema;
- a surrogate that freezes the extremum cells;
- Gaussian queries.
Results:
- Separation Γ_true/Γ_fr ∈ [4/(4+2rM), 64/(9rM)].
- STARVATION: every surrogate-optimal design has ZERO true information; ε-optimal designs leak ≤ 64ε/(9rM).
- Repair frontier R(β) with slope 1/(8rM).
- Sacrifice law N·sac ≥ 8rM log(1/δ); forcing law (log² for square-root forcing).
- The ideal learner attains the true rate; the surrogate-re-solving learner pays log².
- Repair law E|N|·R(b) ≥ D_δ on any channel, with Gaussian attainment.
- "A margin certificate is not a decision": certifying can cost 19–1089× deciding, and is impossible (c ≥ 1) while
  the decision is settled.
Lessons for MARL:
- A1. Starvation ↔ E3 training on the prefix trajectory.
  - Actors, labels and selectors are all trained on the surrogate "the prefix is the delivery".
  - The decision-relevant alternatives (other deliveries, other orders, no delivery) get zero mass.
  - The actor then fits the prefix's side channel (L-90) and is harmed by any other delivery (msguse, L-78, L-85).
  - The repair is β-mixing (the mix actor, p_mix 0.5) or training at the deployment distribution (none/cap6/full, L-105/L-106).
  - Consistent with every E3 result; an analogy, not a transferred theorem.
- A2. "A certificate is not a decision" ↔ direction (b).
  - The sound IBP certificate certifies 1.8–7.7 % of single drops (L-94).
  - The exact simulated decision check allows 9–41 % (L-100).
  - The same shape as A's certificate/decision gap; A's cost ratios are on its own class only.
- A3. Surrogate-re-solving learner ↔ the E3 selectors.
  - They re-solve a critic fitted on the prefix trajectory.
  - Forcing (random candidates) is their only source of off-prefix information.
  - A's lesson: that learner is order-worse, and a design must deliberately SACRIFICE surrogate value.
  - E3 analogue: accept a worse prefix-trajectory fit to learn the off-prefix responses (DAgger B4 did one iteration).

## Paper B (paper_b.tex, read in full): from obstruction to rate
Object:
- finite worlds and safe-answer correspondences;
- an obstruction is a set of worlds with no common safe answer;
- query channels.
Results:
- Lower law cost·t* ≥ ((1−δ)/(|W|−1)) log(1/δ) − log 2, also for unbounded stopping.
- Hellinger tournament upper law; shared blocks cost |Q|·⌈log(|W|/δ)/t*_H⌉.
- PrivateQuery: k private queries force a factor k.
- Order law t* = C h^{2s*}.
- Safe decision Θ(h^{−2}) vs identification Θ(h^{−2(m−1)}) on one channel.
- The QUERY CLASS decides the order (latent family; one parameter of nonlinearity moves h⁶ to h⁴).
- Two layers: the exponent from the order, the constant from a critical game (private vs shared differ by the menu
  size).
- Query design ≡ hitting set, NP-hard.
Lessons for MARL:
- B1. Deciding safely, not identifying ↔ the E3 selectors.
  - A selector need not identify the best edit.  It needs a SAFE answer: never worse than the prefix by more than ε.
  - With oracle needles (+12 … +16 per state) and legal features at chance, {prefix best, needle at c} is an
    obstruction the legal query class cannot separate.
  - The only safe answer is then the prefix, which is what every closed loop shows (L-69/70/78/85).
  - Shape agreement only (L-86).
- B2. The query class is the lever ↔ direction (b) and the proxy.
  - Adding ONE receiver-side query changed what is decidable at the current step: the 1-byte proxy computed on the
    receiver's own view (L-97/L-98).
  - The proxy captured most of the exact current-step oracle; scheduler-side critics were at chance (L-80/L-87).
  - B's lesson: change the query class (who computes what), not the learner.
  - It points to receiver-side tests as the lever for any E3 decision that depends on the receiver's current state
    (L-83).
- B3. Private queries ↔ L-81/L-89.
  - Each candidate edit's value is revealed only by simulating that candidate (private).
  - A value that must be learned per candidate costs in proportion to the candidates.
  - A shared signal (a receiver margin, a sender drift) is what makes a decision cheap.

## Paper C (paper_c.tex; §§1–4, 6–8 read, §5 typed-multiset frontiers skimmed): signed-prefix frontiers
Object:
- one random removal ORDER must serve every budget k;
- a marginal band η: every item is dropped with probability ≈ k/m at every prefix;
- signed weights, regret against the best k-set.
Results:
- Exact frontiers (even: max{2/((m+4)(m−1)), 4(1−η)/(m(m+4))}; odd: two affine pieces).
- Flow equivalence.
- Stability envelope 3ε/d; the price ratio collapses at scale Θ(min{m, 1/ε}).
- Ex-post (budget after the draw) multiplies the free value by m−1, and the band then costs ≤ 1+1/m.
- Knowing the budget is worth NOTHING on a band range.
- ONE EXCHANGE after the reveal recovers the whole budget-aware gain (four items; g_m in even size).
- Weights are KNOWN throughout.
Lessons for MARL:
- C1. E3's protocol is C's structure: commit an order before K, revise R after.
  - C's one-exchange sufficiency agrees with E3's single-swap oracle headroom (+12 … +16).
  - C's premise is known, additive weights.  In E3 the value of a receiver–sender edge is unknown, interacting
    (superadditive in 22/40 states, F5b) and ACTOR-DEPENDENT.
  - So C explains why R = 1 is enough geometrically.  It says nothing about learning which exchange.  That is where
    E3 fails (L-80 … L-89).
- C2. The band ↔ the side channel.
  - C's band forces uniform item marginals: each item dropped equally often.
  - The E3 prefix is the opposite: a deterministic congestion ranking, so "being delivered" carries the ranking to
    the receiver (L-90).
  - A banded (randomised) order removes that channel.  C prices it exactly on its family.  In E3 the price appears
    as actor retraining: prefix actors under a random order are +1.6 … +6.8 % worse (L-101 table; OOD).  A
    random-order-TRAINED actor was planned but not yet trained.
- C3. Stability, and where it ends.
  - The additive price is Lipschitz; the RATIO collapses at Θ(min{m, 1/ε}).
  - E3 analogue: small value perturbations (actor noise, 3-step label noise, sd 6 % per episode) erase ratio-type
    guarantees.  Report additive changes, as E3 does.

## MASTER (master.tex; §§1–4, 6 results, 7 read): the price of a calibration query
Object:
- K groups of m items;
- an ordinary query sees θ_i + b_g, confounded with an unknown group offset;
- a calibration query sees b_g at price κ.
Results:
- NECESSITY DICHOTOMY: an exact witness where every ordinary query has identical means in two worlds with different
  answers, so the value is EXACTLY zero, whatever the sampling.
- Price law Γ* = Δ²/(2K(√(vm)+√(νκ))²), matched and attained.
- Uniform allocation keeps 73.5–100 %; dropping the query type gives 0.
- "The failure is silent because every individual query in it looks useful."
- Misspecifying the separation or contaminating anchors costs an order of magnitude more than the noise shape.
- Calibration is required exactly when the decision is not invariant under the nuisance.
Lessons for MARL (the most directly usable paper):
- M1. The scheduler's view of a receiver is CONFOUNDED with the receiver's unseen current state.
  - The scheduler's packet is one decision old; the phase is wrong 93 % (L-83).
  - The receiver's response to a delivery depends on that current state.  The decision is NOT invariant to it.
  - So every scheduler-side (ordinary) feature set had value ≈ 0 out of sample: v7/v8/pair critics at 0.50–0.53
    (L-80, L-87), legal response head 0.529 (L-89).  They looked useful in sample (TRAIN 0.65–0.73): MASTER's
    silent failure.
  - The receiver-side 1-byte report is the CALIBRATION QUERY.
    - For the current-step drop decision it captured most of the exact oracle (L-98).
    - For edits, an exact reconstruction needs the true own block (324/324, L-83).
  - Prediction: a scheduler-side learner cannot be rescued by more data or a better loss (F1/DFL: confirmed
    negative).  Only a new query TYPE can.
  - Consistent with every E3 learning result.
- M2. MP2's pressure uses downstream WAITING counts (L-114).
  - They are confounded with the downstream intersection's own signal state: a red phase raises waiting.
  - MP2 subtracts them, and its decisions get 14 % worse with any message.
  - The same shape as a contaminated anchor: a quantity that moves with a nuisance enters the decision.
  - A hypothesis, not tested.  A fix to test: pressure on downstream VEHICLE counts, or occupancy.

## SUPPORT (support.tex; §§1–3, 4.1–4.4 sampled, 4.5–4.7 read): deciding vs recovering under one-sided revelation
Object:
- only unsafe tips are revealed;
- name ONE safe tip, not the unsafe set.
Results:
- Decoder risk L/(a+L), depending on the transcript alone; equivariant decoder optimal over ALL rules (least element).
- Decide risk ½(1−P)^N, independent of K; recovery grows (coupon collector, up to 3,699×).
- PAIRWISE SAFETY IS NOT WHOLE-FIBRE SAFETY: a Helly-type three-world witness inside the support-radius model.
- The last revelations carry most of the risk reduction (convex curve).
Lessons for MARL:
- S1. Helly-type failure ↔ multi-receiver E3 decisions.
  - A broadcast drop or edit must be safe for EVERY decoding receiver AND through their interaction in the dynamics.
  - F5b found superadditive multi-receiver gains in 22/40 states; L-96 found droppability falling with the number
    of decoders.
  - A per-receiver certificate (each receiver's L_i) composes for the CURRENT actions, since the actions are
    separable per receiver given the sets.
  - It does not compose for the future: the trajectory couples receivers, hence the veto rate of 56–68 % (L-100).
  - SUPPORT's lesson: certify on the whole fibre, not pairwise.
- S2. Decide ≪ recover ↔ direction (b) vs selector learning.
  - Naming ONE safe drop (is this tail packet safe to skip?) is a decision.
  - Ranking 180 candidate edits is closer to recovery.
  - (b) succeeded legally where (a) failed; the same asymmetry.

## QUERY (query.tex; abstract, §§1–3 read, the rest skimmed by headings): the leakage order is set by the measurement
Object:
- two FIXED worlds whose observation laws are Gaussian mixtures at scale h;
- the admissible query varies;
- the leakage order is the least j with Δ_j ≢ 0.
Results:
- The order is a property of the QUERY.
- Non-vanishing of shifted Hermite sums (the hard half).
- Hellinger sandwich with a shared exponent 2r.
- Matching sample counts; a positive limit constant.
- On one pair of worlds, two legal measurements need 4,678 vs 41,006 samples (8.8×).
Lessons for MARL:
- Q1. The message PAYLOAD is the admissible measurement of a neighbour's state.  It is fixed at 25 B: phase, time in
  phase, and vehicles and waiting per approach summed over lanes.
- QUERY's lesson: the decision's difficulty can be set by WHICH summary is legal, not by how many are sent.
- Untested in E3; every E3 experiment kept the payload fixed.  Two observations make it relevant:
  - the MP2 controller is harmed by the waiting summaries it reads (L-114);
  - an actor given all payloads gains only 2.5–8.6 % over none (L-105/L-110).
- A candidate lever: a decision-relevant payload (per-movement downstream occupancy, or the sender's own next phase:
  intent) at the same bytes.
- Consistent with the "query class is the lever" of B and the calibration-type query of MASTER.

## STRUCTURAL (structural.tex; abstract and intro read): one schedule, or a menu, for signed budgets
Object:
- a schedule reveals items one at a time;
- a client with budget k sees the first k;
- the items carry SIGNED weights that cancel.
Results:
- V_avg = 2/((m+4)(m−1)) and V_path = 2/(m+4), both attained; V_path/V_avg = m−1 exactly.
- A schedule that pays nothing at any budget must move the prefix sum by at most 2 per element.
- A MENU of five rankings is necessary for every ε < 1/114.
- DP over prefix-sum summaries for m ≤ 120.
Lessons for MARL:
- T1. Signed value per delivered packet ↔ E3's non-monotone budget curves.
  - Delivering one more packet can HURT a prefix-trained actor (msguse full > prefix; L-90 side channel).
  - The blind cap curve is not monotone (scratch s3: cap 4 +2.7 % vs cap 5 +8.3 %, L-98).
  - STRUCTURAL's regime is exactly that: one committed order that is good at one capacity can be poor at the next.
  - The prefix is ONE order serving every receiver capacity k_i ∈ 1..7.
  - The paper's remedy is a small MENU of orders.  In E3 terms, a per-capacity delivery rule.
  - Or, as the co-design results suggest, an actor trained so that value is monotone in information (the full
    actor): the signed regime is created by the actor, not by the traffic.

## FUNCTIONAL (functional.tex; abstract read; its Lean CertificateLifetime / SelectiveMaintenance / ResidualMaintenance modules read earlier, MARL_LEAN_CORPUS_READ): the pair-flip proxy at frozen extrema
Object:
- certify the Top-k of relations ranked by range;
- the scalar pair-flip proxy is computed at the CURRENT extrema with ordering constraints dropped.
Results:
- The proxy is wrong in BOTH directions (ratio → 0 and → ∞ on explicit families): a bound in neither direction.
- The true alternative set is a finite union of convex pair regions.
- KKT certificate under PSD only.
- 6,000 random instances: 12.3 % off by more than 2×.
- The cause is always that the cheapest alternative MOVES an extremum.
- Plus (modules): certificate lifetime under bounded drift; selective refresh.
Lessons for MARL:
- F1. A proxy at the current state fails exactly when the relevant quantity moves ↔ (b)'s current-step check.
  - It is valid now and vetoed by the future in 56–68 % of steps (L-100).
  - The same failure appears in the selectors' 3-step label vs the full episode (Spearman 0.39–0.61, L-73).
  - FUNCTIONAL's remedy: certify against the whole moving alternative set.
  - E3's analogue is the lifetime certificate (LeanMarlDecisionCertificateV1), and its legal approximation is the
    staleness bound (proxyage, L-98/L-104), a SelectiveMaintenance-style refresh rule.

## ADAPTIVE (adaptive.tex; abstract read): stopping and tracking, the three unproved steps
Object: the analysis of an adaptive allocation, covering its concentration, its expected stopping time and tracking.
Results:
- Layer-cake identity for the expected stopping time.
- Concentration from a sub-Gaussian hypothesis.
- Existence of an integer allocation with per-arm deficit ≤ 1.
- The largest-deficit rule VIOLATES it: a five-arm witness at 26/23, and 375,239 of 1,228,079 targets violate.
- The Balinski–Young quota method violates neither bound.
Lessons for MARL (weak):
- The staleness bound of (b) is a refresh-TRACKING problem: every receiver–sender pair should be refreshed at a
  target rate within its capacity.
- ADAPTIVE: the natural largest-deficit rule is not within quota, and a quota method is.
- A legal refresh scheduler with a provable per-pair staleness bound is an apportionment problem.
- A way to make proxyage's bound principled.  Untested.

## D6 (d6.tex; abstract read; its 267 modules summarised in MARL_LEAN_CORPUS_READ): scalar queries, slices and a sharp margin
Results:
- A bound over a two-parameter SLICE says nothing outside it.  Here the slice is proved to be the minimum.
- FITTED design weights are evidence, not a derivation; D6 derives them.
- Exchange bound 2(L_F(T) − L_F(S)) ≤ |T\S|(2δ − μ).
- SHARP threshold: a margin 2δ suffices for Top-C optimality, and below it Top-C can be strictly suboptimal.
Lessons for MARL:
- D1. The F5 bridge's scores were FITTED after seeing the whole value table.  The manuscript already says it is
  "a numerical instantiation, not a certificate" (L-36).  D6 says the same.
- D2. E3's prefix is Top-C by the cached-queue score.
  - D6 requires a cut margin ≥ 2δ, where δ bounds the interaction (mixed differences).
  - E3 has tiny margins (1.4–5 % of states within 1 of the best) and large interactions (F5b superadditivity).
  - So D6 predicts no optimality guarantee for the prefix: consistent with the oracle headroom.
  - It says nothing about learning the correction.

## UNIFIED (unified.tex; §§1–5 read; the rest by headings): the six strands in one question
Results:
- SUPPORT DECOMPOSITION: L_K(T) − L_K(S) = the full-domain difference + (D_K(S) − D_K(T)).
- A zero-interaction witness where Top-C is right on the cube and the WORST on the support; the exchange bound holds
  with equality, so the geometry term cannot be dropped.
- The computable span-based κ is VACUOUS (0/919 firings).  The exact κ fires (779/919) at C(m,k) cost.
- The cheap SINGLE-SWAP surrogate is UNSOUND once the budget exceeds one.
- Certifying costs more than deciding (12× → 1089× → ∞ while the decision stays settled).
- Calibration under a nuisance offset: Γ_comp = 9Δ_dec²/(2(σ√c_o + ν√c_a)²).
- A PHASE IN WHICH NOTHING SHOULD BE MEASURED (ε ≥ ½).
- Obstruction criterion; randomised error floor 1/|H|.
Lessons for MARL:
- U1. Support ↔ training/deployment distributions.
  - A prefix-trained actor is optimal "on its support" (prefix deliveries) and worst off it (full, edits: msguse,
    L-78/L-85).
  - The selectors' labels and critics live on the prefix trajectory's support.
  - UNIFIED's identity says the gap is a separate, non-removable term.
  - E3's remedy is to change the support the actor is trained on (L-105/L-106/L-111).
- U2. "A phase in which nothing should be measured" ↔ the none actor (0 B) is the best capacity-respecting system
  found (L-105/L-109).  In E3 the nuisance is the random receiver capacity plus the prefix's selection.
- U3. The single-swap surrogate is unsound ↔ E3's candidate family.
  - The family is one-swap and radius ≤ 2 profiles.  F5b found coverage outside it ≥ +4.0 … +5.3, and a local search
    reaching 85 %.
  - UNIFIED's warning applies to any certificate built on single swaps.
- U4. Certifying ≫ deciding ↔ L-94 vs L-100 (as A2).

## Consistency across MARL results and the papers (19:5x)
Mutually consistent groups (the same mechanism seen several ways):
- G1: harm from off-prefix inputs.
  - msguse: full delivery is worse than the prefix for prefix actors.
  - The fresh-flag side channel (L-90).
  - A none-trained actor beats every prefix actor (L-105/L-109/L-113).
  - Papers: A1 (starvation), U1 (support term), T1 (signed budgets).
- G2: selectors fail.
  - Closed loop worse than the prefix (L-69/70/78/85).
  - Critics at chance out of sample, 0.65–0.73 in sample (L-80/L-87).
  - The scheduler lacks the receiver's current state (L-83); the legal response head fails (L-89).
  - Papers: M1 (a missing query TYPE; silent failure), B1 (obstruction).
- G3: the headroom is action perturbation.
  - Blind forcing reaches the same oracle (L-81).
  - Q̂ is learnable (L-88); message steering ties a zero-byte override (L-91).
- G4: certify ≫ decide.
  - IBP certifies 1.8–7.7 % (L-94); the exact decision check allows 9–41 % (L-100).
  - Papers: A2, U4.
- G5: the current step is not the future.
  - Veto 56–68 % (L-100); the Lean counterexample; the 3-step label vs the episode (L-73).
  - Papers: F1 (moving extrema).
- G6: MP2 is harmed by messages.
  - −14.2 % without them (L-114).
  - MP2 IMPROVES by 3–7 % under delayed observations (A4 delay test).
  - The BC actors cloned from MP2 are the worst actors and lose to maxq (L-115).
Contradictions / tensions with written claims:
- X1. Abstract, A1, §E3, fig. e3a: "max pressure has 9.5–24 % more waiting than each learned actor".
  - Against the same heuristic without messages: BC actors +1.2 … +5.5 % WORSE; scratch actors −1.7 … −6.3 % (L-115).
  - The claim is true only against a message-harmed baseline.
- X2. Gate G1 is read as "the actor uses messages", and the paper's premise is that communication matters.
  - An actor TRAINED without messages is 8 % better (L-105).  G1 measures input dependence, not value.
  - The consistent test is co-trained comm vs co-trained none at equal training.
- X3. Gate G2 ("within 10 % of max pressure", on SELECT) is measured against the weakened baseline and on the
  checkpoint-selection split (L-111 shows SELECT optimism).
- X4. The fixed-MP2 track (M1, M2, fig. 1's "gain through the cache") studies a controller whose communication is
  harmful.  Its headroom partly measures reducing that harm.  Not re-analysed.
- X5. (b)'s only legal non-inferiority result (L-104) is on the BC actors, which a 0-byte heuristic already beats.

## The list of places where the problems can be (P1–P17), with status
| # | where | evidence | status |
|---|---|---|---|
| P1 | reference controller MP2: approach-level pressure on downstream WAITING, harmed by messages | L-114, L-115 | demonstrated baseline defect |
| P2 | protocol + training: capacity-respecting communication is net-NEGATIVE for learned actors | L-105/L-109/L-113; L-106/L-108/L-111 | replicated development finding |
| P3 | gate G1 measures input dependence, not benefit | L-105 vs msguse | design flaw of the gate |
| P4 | priority side channel in the fresh flag | L-90 | mechanism (one actor) |
| P5 | the selector target is action-perturbation headroom (policy improvement), not information value | L-81, L-88, L-91 | shown for scratch s3 |
| P6 | the scheduler's information is confounded with the receiver's current state (a missing query TYPE) | L-83, L-89; M1 | shown |
| P7 | label/objective mismatch (3-step or held phase vs episode) | L-73, TARGET_DIAG | shown |
| P8 | labels and critics only on the prefix trajectory's support (starvation) | L-84 (Spearman 0.27), A1, U1 | shown |
| P9 | SELECT-split optimism (checkpoint and τ selection) | L-111 | shown once |
| P10 | statistical power: 32-episode panels (±2 %), per-episode sd ≈ 6 %; the reserved 1301–1316 panel is too small for a ±1 % margin | L-98 | design risk |
| P11 | capacity process k_i i.i.d. U{1..7} EVERY step: maximally inconsistent inputs | hypothesis from P2 | untested |
| P12 | actor architecture: flat MLP over fixed slots | set actor running (L-112) | testing |
| P13 | payload content (approach sums of vehicles/waiting) may not be the decision-relevant measurement | QUERY lesson; L-114 | untested |
| P14 | single-swap / radius-2 candidate family (coverage ≥ 4–5 units missing; single-swap surrogates unsound) | F5b, U3 | shown (coverage) |
| P15 | theory hypotheses not instantiated (ε of SafeEdit; ScoreLocal fitted post hoc) | T1/T4 status | known, stated |
| P16 | (b)'s Lean guarantee covers only the simulated certificate; the legal rules have none | L-92, L-94 | known |
| P17 | the BC recipe clones the harmed MP2 | L-115 | demonstrated consequence of P1 |

## Solutions suggested by the papers, and what is being validated
- P1 → MASTER M2 (a contaminated anchor).
  - Validate: pressure on downstream VEHICLES; a lane-level variant.
  - Re-baseline every claim against maxq and the corrected MP.  [running next]
- P2 / P11 / P12 / P13 → change the SUPPORT / the query (A1, U1, U2, Q1, T1).
  - Validate:
    - fixed-per-episode capacities (P11);
    - random-order training (C2 / P4);
    - the set actor (P12, running);
    - an intent payload (P13, heavier, later).
- P3 → redefine the communication gate as co-trained comm vs co-trained none at equal training.
- P5 → report the zero-byte override for any value-based selector (L-91).
- P6 → a receiver-side calibration query (M1).  The proxy shows it works for current-step decisions (L-98).
- P7 / P8 → A's repair: on-policy (DAgger) labels plus β-mixed exploration.
- P9 / P10 → independent 128-episode panels (done in development); a larger confirmatory block (authors).
- P14 → certify on the whole fibre (S1, U3).

## External literature checked for the problem list (19:5x)
- Lowe, Foerster, Boureau, Pineau, Dauphin, AAMAS 2019, arXiv 1903.05168.
  - Agents can APPEAR to communicate (messages predict their own actions) while the messages have no effect.
  - Listening/signalling metrics can mislead; causal influence and ablations are needed.
  - This is P3: E3's gate G1 is a listening metric (removing inputs changes actions and waiting).  It does not show
    that communication helps.  The consistent test is a co-trained no-communication agent.
- Zhang, Zhang, Lin (VBC), NeurIPS 2019.  A fair amount of communication is noisy and redundant; eliminating it gives
  both efficiency and performance gains.  Consistent with P2.
- Sun, He, Wang, Zheng (DRMAC), arXiv 2501.02888, 2025.
  - Even with gated messages, decision-irrelevant dimensions and confounders at the RECEIVER degrade decisions.
  - Remedy: redundancy reduction and dynamic dimension masking.
  - Consistent with E3: masking non-neighbour slots (nbrmask) turned +6.5 % vs none into a tie (L-108 → L-111).
- Kim, Cho, Sung (Message-Dropout), AAAI 2019, arXiv 1902.06527: block-wise message dropout during training improves
  learning speed and final performance.  A candidate for P2 and P12, untested.

## Validation status of the solutions (19:5x; updated as results arrive)
- P1 (baseline):
  - Fixing pressure with vehicle counts is WORSE (L-116); the "contaminated anchor" hypothesis is refuted.
  - Validated correction: use maxq (no messages) as the heuristic reference.
  - Re-baselined (L-115): BC actors lose to it, scratch actors win by 2–6 %, none / nbrmask actors by 12–14 %, full by
    15–20 %.
- P2 / P12 (communication hurts learning; architecture):
  - The set-structured actor (shared per-sender encoder, heard-masked pooling) under the PREFIX reached select 1256 at
    iteration 1160.  The flat prefix actor was about 1560 at 1000; the none actor's best is 1245.
  - Pending: final and 128-episode evaluations; set actor under none (same architecture) as the fair reference;
    set actor under nbr; nbrmask seed 1.
- P3 (gate): replaced by co-trained comm vs co-trained none (L-105/L-109/L-113); every flat comm actor loses.
- P4 / P11: the random-order actor and the fixed-capacity actor.
  - Trainer v6 (`--capacity`) and eval v5 are written and identity-checked (v6 prefix iid reproduces select
    4089.1875; eval v5 iid parity passed).
  - To launch when cores free.
- P5, P6, P9: done (L-91, L-98, L-111).

## The papers-prescribed design (20:0x), after the user's question "why not avoid what the papers predicted?"
| paper lesson | pitfall it predicts in E3 | prescription | experiment |
|---|---|---|---|
| MASTER (missing query type ⇒ value 0, silently) | the scheduler cannot see the receiver's state; the MP2 baseline fails silently | put the choice where the information is; audit the reference | receiver-side decoding rxq (set actor); maxq baseline (L-115) |
| B (query class is the lever; obstruction) | scheduler-side selection at chance | a receiver-side query | the same rxq; the proxy (L-98) |
| A (a surrogate starves decision cells; repair by sacrificing surrogate value) | actor and labels only on the prefix support | train on the deployment support; β-mixing | co-trained actors (none/full/cap6/nbr/rxq); mix |
| UNIFIED (support term; a phase where measuring nothing is optimal) | comm actors worse than no comm | the none control first; measure only what pays | none/set_none controls (L-105/L-109) |
| DRMAC / UNIFIED (irrelevant dimensions hurt the receiver) | flat MLP over 8 fixed slots | mask / structure the receiver's input | nbrmask (L-111), set actor (L-112) |
| C (a band removes order information) + Message-Dropout | the fresh flag leaks the priority | random order in training | random-order actor |
| STRUCTURAL / FUNCTIONAL (signed budgets; proxies at a moving state) | k_i redrawn every step makes inputs inconsistent | consistent capacity per episode | fixed-capacity actor |
| QUERY (the measurement sets the order) | the payload may not be decision-relevant | a receiver-relevant payload | not yet (protocol change) |
