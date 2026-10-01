# Corpus ledgers re-read for the MARL relay paper (30/09/2026, from 15:1x EDT; running notes)

Purpose (user 15:1x): re-read the old papers' texts AND their ledgers (what succeeded, what failed, how it was proved, the
conclusion of each step), validate the parallel session's "applies to MARL" table (ledger L-167), and note what can
really strengthen the MARL paper.  Every note says what the source proves, what it does NOT, and how (or whether) it maps
to E3.  "Maps" means a structural correspondence with a checkable prediction; it is NOT a transferred theorem (L-86).

Sources read so far:
- the paper texts `research/papers/_tex/{paper_a,paper_b,paper_c,master,query,structural,functional,d6,support,adaptive,unified}.tex`
  (abstract, every theorem-like statement, limitations; extracted by a script, then read);
- `research/papers/DOSSIER.md` (whole);
- `research/papers/CLAIMS.md` (Paper A rows A1–A24, Paper B rows B1–B25, Paper C rows C1–C21);
- `work/p13_conjectures/LeanAdaptiveTrackingV1.lean` (statements and docstring).

---------------------------------------------------------------------------------------------------------------------

## Paper A: the price of a frozen surrogate (separation, starvation, repair)

**What it proves (Lean, `LeanPaperACentredV1`, `LeanPaperAFrontierV1`, `LeanPaperAStrictV1` …):**
- On one centred construction, `Γ_frozen = 9/512` exactly; `9/(128(4+2rM)) ≤ Γ_true ≤ 1/(8rM)`.  The ratio is Θ((rM)^−1),
  already at M = 1.
- **Starvation:** every surrogate-optimal design puts ZERO mass on the middle pairs, so its true information is exactly 0.
  Every ε-optimal design has true information ≤ 64ε/(9rM).
- **Repair frontier:** sacrificing β of surrogate value buys true information between 9β/[128(4+2rM)] and β/(8rM).  The
  value is linear in β with the separation's own 1/(rM).  There is **no threshold** (Prop. "no threshold, linear repair":
  every budget b > 0 buys J_t > 0).
- Sacrifice law and repair law for adaptive policies (N·sac ≥ 8rM·D); the frontier is the optimal budgeted rate on
  Gaussian cells.

**What failed or was retracted along the way** (DOSSIER §1, CLAIMS A-rows):
- "a positive bracket gap forces the learner to be slower": false (direction);
- the "8.0e-3 plateau is structural": false (method; fell to 5.0e-7);
- "Λ_proxy is the frozen set by inspection": false, with an explicit counterexample;
- `AnchorMonotone` fails at the boundary, so the first starvation route did not apply to the real surrogate; it was
  replaced by the centred construction;
- a sample-cost separation (Ω(log²(1/α))) is NOT claimed: static starvation does not give it without a policy link.  The
  link was later assembled only for one learner (A24: this oracle, this exploration rate, this tracker).
- The learner panel is below uniform by 19–23 %, but not significant after Holm correction.

**Method lessons:** state both games on ONE model and one parameter class; restricting an infimum raises it; closed vs
strict alternative sets matter; every transferred bound needs its hypotheses instantiated at the object being criticised.

**MARL mapping (my reading, stronger than L-167's codebook reading):**
- The E3 stream order is a FROZEN SURROGATE of "who matters": the cached-queue ranking computed from the scheduler's own
  cache.  At low capacity it starves the low-ranked senders: under cap4 with a sticky order about 46 % of (receiver,
  agent) pairs are NEVER covered (traffic-free simulator, L-168).  That is Paper A's starvation phenomenon: zero mass,
  zero information, not merely a small amount.
- The repair is a β-mixture with a uniform or rotating design.  Paper A predicts, in its own model, linear repair with no
  threshold.  E3 has already measured the two ends: the full rotation (agefirst) is the β = 1 end; its iid cost of +0.3 …
  +0.5 % (L-169, L-175) is the SACRIFICE, and the gain at cap4 and low is the repair.
- **Testable prediction (new experiment V-A):** a β-mixed order (with probability β use the rotation, else the
  cached-queue ranking) should give coverage of the starved senders that rises linearly from 0 at small β (no threshold),
  and low-capacity waiting that improves already at small β; the iid cost should grow with β.  This is a DIRECT check of
  the frontier shape, measured at information level (coverage, age; exact via AgeMirror) and at decision level (waiting).
- What does not transfer: the exact constants (they belong to the centred construction), the Gaussian-cell rate theorem,
  and the sample-cost laws.  In E3 "information" is coverage and age of relay summaries, not KL.
- L-167 mapped Paper A to "refit the codebook on the student's states".  The parallel session found that A-fit reproduces
  v1's cut points exactly, so that intervention is weak.  The order-starvation mapping matches Paper A's actual theorem
  (optimal design of a frozen objective gives zero mass to the decision cells) much better.

## Paper B: from obstruction to rate (the safe-order law)

**What it proves:**
- Safe-order law: order s suffices iff every obstruction contains a pair separated at order s, so
  `s* = max_H min_{w≠w'∈H} sep(w,w')`.
- Lower law (KL/χ² per query, any randomised adaptive policy, including unbounded stopping) and upper law (tournament of
  LRTs with shared blocks, at most |Q|·⌈log(|W|/δ)/t_H*⌉ rounds).
- Decision order 1 versus identification order m−1 on the parity family.
- Query design is an order-thresholded hitting set, which is NP-hard.
- "Adding queries never raises the decision order."
- A zero-query floor: with answers "not w", a query-free guess is unsafe with probability exactly 1/m, so no lower bound
  holds above that floor.

**What failed or was retracted:**
- the old `hdiff` was unsatisfiable (a first difference is not a density);
- the degree-capped class refutes the 2r law (measured order 3.94 < 6);
- "8.13" was an implementation artefact (cancellation in 1 − affinity), and the corrected value is 5.80;
- the "within a factor two" check tested one side only;
- the geometry and the observation order lived in two constructions that were not joined; the partition was first
  posited on the world index and later derived (B9, B22);
- the continuous-transcript chain rule was open for long, and was closed by the change of measure on a filtration (B20).

**MARL mapping:**
- A receiver's action is the "safe answer"; neighbour states are the worlds; a message field is a query.  The safe-order
  law says that a summary needs to separate only the OBSTRUCTIONS: sets of neighbour states with no common good action.
  It does not need to identify the state.  That is the formal reason 3 B summaries can be enough (compression cost −0.2 %,
  BYTEBUDGET vs raw, 5/5 seeds).
- **Testable prediction (V-B):** inside one codebook cell (states that map to the same 3 B code), the TEACHER's action
  should rarely differ.  Measure the "obstruction rate": the share of teacher-action disagreement between raw payloads
  that share a code, compared with pairs in different cells.  B-fit (field sensitivity, parallel session) is a local
  proxy of the same thing.  A low within-cell disagreement is the empirical content of "the code resolves the
  obstructions".
- The zero-query floor maps to the 0-byte student: a policy without messages has an error floor wherever an obstruction
  hides inside a local-observation class.  That is the principled definition of "communication value over the 0-byte
  student".  It is an exact counterpart of UNIFIED's `classes resolve iff no obstruction hides` and `randomised error
  floor 1/|H|` (below).

## Paper C: exact marginal-regret frontiers for signed-prefix compression

**What it proves:**
- ONE random order must serve every budget, with a marginal BAND (each item's retention probability nearly uniform at
  every prefix).  Regret is measured against the best subset at each budget.
- Exact V_m(η) (even and odd), zero-band values, and the free threshold.
- Flow equivalence: m! rankings reduce to O(m^d) count states for d types.
- Stability with the normaliser moving, and a robust-ball rate Θ(min{m, 1/ε}).
- Ex-ante vs ex-post objectives: the ex-post free value is (m−1)·V_free.
- Knowing / editing / committing (the sandwich): one exchange after the reveal recovers the budget-aware value on four
  items and, in even size, on the family.

**What failed or was retracted:**
- C4's flow-to-ranking theorem had an EMPTY feasible class (`countFeasible_empty`), so it said nothing; it was repaired
  with a finite horizon;
- C8 was first stated where its hypothesis is unsatisfiable (vacuous exactly where wanted), then restricted to a
  band-feasible subset with a satisfiability witness;
- C9 first described a position band and wrongly claimed the endpoint indicators were exclusive;
- "no family loses half the price" read only the structured families;
- the floor was reported outside its proved domain.

**Method lessons:** every transferred hypothesis needs a satisfiability witness (the vacuity defects); instantiation
bridges (C10, C19–C21) are where the time goes.

**MARL mapping (validating L-167 (a)):**
- The STRUCTURE matches exactly: HETERO_v0's committed broadcast order is one order serving every receiver's budget K_i.
  Paper C's "budget revealed after the order" is HETERO_v0's commit-then-reveal, and Paper C's "one exchange after the
  reveal" is HETERO_v0's revision allowance R.
- **Paper C's BAND has an E3 counterpart that L-167 did not name:** "every sender's probability of being inside the
  decoded prefix is nearly uniform over time".  That is what the rotating head (agefirst) enforces, and the congestion
  order violates.
  - Paper C computes the STATIC price of such a band against the unconstrained best order.  In E3 that is the iid cost of
    rotation (+0.3 … +0.5 %).
  - The DYNAMIC benefit (bounded age, coverage) is not in Paper C at all.  It is the ADAPTIVE/AoI side.
- L-167's claim "the regret collapses to ≈ 0 when every packet is complete" is TRUE BUT TRIVIAL in Paper C's model:
  complete, fresh packets make every subset of the same size equivalent, so any order is optimal.  It is not a
  consequence of Paper C's frontier theorems.  The nontrivial part in E3 is that relay packets are complete but carry
  AGED copies, so subsets differ by freshness; that is a dynamic effect outside Paper C.
- Paper C's exact frontier theorems (g_m family, signed weights, one value vector for all budgets) do NOT transfer.  E3
  receivers have DIFFERENT value vectors (neighbours matter differently), so E3 is a multi-receiver menu problem
  (STRUCTURAL) rather than Paper C's single-vector problem.
- What can be used honestly: the general results that hold for EVERY weight vector:
  - flow equivalence for typed multisets (typedflow);
  - the free-threshold theorem;
  - additive-price stability;
  - the knowing / editing / committing sandwich.

  With sender TYPES (neighbour / non-neighbour × fresh / aged), an E3 instance could be computed exactly by the flow
  program from measured type weights.  That would be a real application, though a secondary one.
- **Testable prediction (V-C):** the static price of the band (the iid cost of rotation) should shrink when every packet
  is complete (relay) compared with the raw one-sender packets, because the per-receiver value then depends little on
  which senders are decoded.  Measure the iid cost of agefirst for relay students (+0.3 / +0.5 %, L-175) against the
  same cost for a non-relay FO student under the same orders.  L-128 D4a has FO under several orders at iid:
  −0.3 … −0.6 %, i.e. no cost.  So this prediction is ALREADY in tension with the data: rotation costs nothing for FO and
  a little for relay.  It must be reported as a non-confirmation unless a clean test says otherwise.

## ADAPTIVE: largest-deficit tracking does not achieve unit quota error

**What it proves:**
- layer cake for ℕ-valued stopping times;
- a geometric tail bounds the expectation;
- finiteness from the tail;
- a sub-Gaussian threshold;
- deficits sum to zero, so some arm is always behind (`exists_deficient`);
- `tracking_bound`: an allocation squeezed between ⌊t w_i⌋ and ⌊t w_i⌋+1 has deficit ≤ 1;
- `tracking_exists`: for every target and horizon SUCH an allocation exists (by construction, not online).

**The paper's headline is NEGATIVE:**
- the natural ONLINE rule, serve the largest deficit, VIOLATES unit quota error (exact 5-arm witness, 26/23 at horizon
  11; 375,239 of 1,228,079 targets violate; the worst plateaus near 2, not K−1);
- Jefferson's rule and Balinski–Young's quota method do not violate.

**Validation of L-167 (b)** ("age-first = greedy most-deficient tracking with uniform targets … with K_i ≥ 1 it bounds
every sender's head-gap … deficit ≤ 1"):
- PARTLY WRONG as sourced.  `tracking_bound` is about an allocation squeezed between floor and floor+1.
  `tracking_exists` is a per-horizon, NON-online existence.  The paper proves the greedy online rule does NOT meet
  deficit ≤ 1 in general.
- For UNIFORM targets the greedy rule is round-robin, and the bound is then elementary (round-robin keeps counts within
  1).  It does not come from ADAPTIVE's theorems, which are about the failure for NON-uniform targets.
- So the honest use is the reverse of L-167's.  If E3 wanted NON-uniform injection rates (important senders more often),
  ADAPTIVE warns that the natural online "oldest/most-deficient first" rule can drift past unit error.  Its census gives
  the size (up to about 2).  A quota-method rule (Balinski–Young) is the safe choice.
- The age bound itself must be proved for the E3 dynamics directly: prefix decoding, relay merge, K_i ≥ 1.  It is not
  inherited.

## FUNCTIONAL (paper: "the scalar proxy fails in both directions"; ledger 02_FUNCTIONAL A–I; Lean `LeanFunctionalCertificateLifetimeV1`)

**What the paper proves:**
- the pair-flip proxy can be wrong by a factor → 0 or → ∞ (two exact families);
- the true alternative set is a finite union of convex pair regions;
- shrink/expand closed forms;
- KKT sufficiency under positive SEMIdefiniteness.

**The ledger's arc:**
- an "ablation that was never an ablation": an order-preserving transform left an ORDINAL allocation byte-identical;
- a policy starved by construction;
- a forced exploration floor rescues the starved policy and COSTS the well-targeted ones, the oracle most: "a mandatory
  exploration fraction is not free";
- censoring first read as a property of the family, which was wrong (the budget was binding);
- paired comparisons under common random numbers beat marginal medians;
- the final advantage belongs to ONE policy (C_anytime), not to "adaptive policies" as a class.

**The certificate-lifetime module** (the thing L-167 (c) cites; it is part of the FUNCTIONAL strand, not of the paper
text):
- LIFE2: if the gap g > 2(δ + drift), both the estimate and the future response keep the same extrema;
- LIFE3: a per-step drift ν gives drift ≤ h·ν over h steps;
- LIFE4: a certified lifetime H* with 2(δ + hν) < g;
- LIFE5: the future top-K is kept if the margins exceed estimate plus drift errors.

**Validation of L-167 (c)** (composite: margin > 2L(κ + H_max ν) ⇒ the relay-view action equals the fresh-full action):
- STRUCTURALLY VALID.  LIFE2/LIFE3 are about any score function on a finite action set, which is exactly the actor's
  logits; the MARL module adds `argmax_stable_lipschitz` and `lifetime_from_drift_rate`.
- What is NOT given: δ (the logit error from 3 B quantisation at age 0), ν (the logit drift per step of relay age), and
  L.  In E3 these are properties of data and of the actor, to be measured.  The corpus's own open gap is the same: "how
  coverage and the drift bound are learned, and at what cost, is unproved" (02_FUNCTIONAL §72).
- The informative experiment is NOT to check the implication itself (on a sample where 2G < g, agreement is a
  mathematical identity).  It is a PREDICTIVE certificate: estimate δ and ν on TRAIN episodes, predict the certified
  decisions on held-out episodes from their ages, and report soundness (certified ⇒ same action) and coverage.  Then
  compare the prefix order with the rotation: shorter ages mean more certified decisions.  This is V-F below.

**New lesson for E3:** the forced exploration floor's cost is the iid cost of rotation.  "Not free, and costs the
well-targeted policy most" is the right way to report +0.3 … +0.5 %.

## SUPPORT (decide without identifying; ledger 03_SUPPORT A–C)

**What the paper proves:**
- exact decide risk ½(1−P)^N, flat in K, while recovery grows (coupon collector);
- the equivariant decoder is optimal;
- pairwise safety is not whole-fibre safety (the three-world Helly-type witness).

**The ledger's arc:**
- a controller exists iff every observation fibre has a common safe action; this is standard, and the novelty was
  relocated to the concrete instance;
- the obstruction was realised in the actual support geometry;
- "obstruction ORDER does not determine query cost", both directions (a large obstruction can be answered by one query;
  a tight law can track a different quantity).

**MARL mapping:**
- Whole-fibre, not pairwise: to claim that a 3 B code or a 0-byte policy is sufficient, every observation class (all
  states giving the same code, or the same local view) must admit a common good action.  Pairwise checks do not suffice.
- The "obstruction order ≠ cost" warning forbids the easy story "bigger neighbour conflicts need more bytes".

## STRUCTURAL (one schedule cannot serve every budget; ledger 04_STRUCTURAL A–G)

**What it proves:**
- the exact menu law under signed cancellation;
- the staircase gives χ = r;
- five rankings are needed for ε < 1/114;
- the exact normalised tolerance curve for the staircase is **χ_ε = r for ε < 1/(2r) and 1 for ε ≥ 1/(2r)**: a collapse,
  not a trade-off;
- curve richness tracks coefficient PRECISION, not width.

**Novelty lessons recorded by the chain itself:** "one ordering serving every budget" is studied in incremental
submodular maximisation; antichains of distinct-size sets are a known circle; the target worth pursuing is
representability.

**MARL mapping:**
- The E3 question "do receivers need their own orders (a menu), or does one broadcast order suffice?" is exactly this.
- STRUCTURAL's positive side: with NON-NEGATIVE weights, one well-chosen order degrades gracefully.  Signed cancellation
  (extra items can hurt) is what forces menus.
- E3 has both regimes, measured:
  - flat actors and stale caches make extra messages HARMFUL.  The set actor's budget frontier is non-monotone, cap4
    worse than cap2 and none (L-119).  That is the signed regime;
  - fresh-only or relay receivers make extra decoded packets (weakly) helpful.  That is the monotone regime, where one
    order suffices.
- **Testable prediction (V-S):** the per-receiver budget frontier (waiting against the number of decoded packets
  K = 1 … 7) should be NON-monotone for stale-kept or flat actors and MONOTONE for relay students.  Under relay, per-receiver
  menus (rxold, nbr) should add nothing over one order, at every K.
- The tolerance collapse is the precise form of "one order is enough up to ε".

## QUERY (the admissible measurement sets the leakage order; ledger 06_QUERY A–D)

**The ledger's arc:**
- every cell was degenerate because the estimand (one-step reward) was constant;
- raising the horizon (1, 4, 8) did not help, because the continuation policy was NOOP;
- the state distribution was the binding constraint;
- a positive control produced the first evaluable cells;
- the novelty was relocated to Blackwell–Le Cam deficiency, then narrowed ("naming is not an equivalence").

**MARL relevance:**
- E3's H = 3 continuation labels were this same failure mode: a proxy estimand.
- The QUERY natural-panel statistic (other agents' actions matter in 5 % of states at h = 1 and 28 % at h = 6; L-123)
  is the one number to cite about how sparse a coupling signal can be.  E3's is dense: 34.5 %.

## D6 (the slice is not a restriction; the margin threshold is sharp; ledger 05_D6 C–Q)

**What it proves:**
- the margin-sensitive exchange 2[L_F(T)−L_F(S)] ≤ |T∖S|(2δ − μ): a margin 2δ is sufficient for Top-C optimality, and
  every sub-threshold margin fails (sharp);
- the cyclic phase design attains the linear lower bound (optimal in its class);
- an integer-budget greedy law;
- discovery, revalidation and anytime control are closed as a chain; regret inside correctly labelled epochs is open;
- many retractions: D6-prime false, the (m−1) law false at m = 4, an "exchange rate −k" withdrawn, several vacuous
  bridges demoted.

**MARL mapping:**
- The sharp 2δ threshold is the Top-C version of the argmax 2ε margin in `LeanMarlDecisionCertificateV1.argmax_stable`
  and of SafeEdit's `threshold_sharp`.  The composite lifetime certificate uses the same shape (V-F).
- The top-K receiver menus (rxq, nbr) are D6's Top-C selection.  Its exchange bound says Top-C by score is optimal when
  the score margin exceeds twice the interaction, which is why per-receiver menus gain ≤ 0.6 % in E3 (L-128 D4a) if the
  interactions are small.  That link is not measured.

## UNIFIED (the information cost of a compression decision)

**What it proves:**
- support decomposition;
- certifying a margin costs more than deciding (a ratio up to 1089);
- **classes resolve iff no obstruction hides inside a class; any randomised rule leaves unsafe mass ≥ 1/|H| on an
  obstruction H**;
- a phase in which the optimal design measures NOTHING.

**MARL mapping (the principled definition of communication value):**
- A 0-byte policy is safe iff no obstruction hides inside a local-observation class.  Where one does, every 0-byte rule
  has error ≥ 1/|H| there.  Messages are worth their bytes exactly on those classes.
- The distilled 0-byte student is the empirical best 0-byte rule.  The teacher-versus-student action disagreement marks
  where local information does not resolve the teacher's decision.
- **Testable prediction (V-U):** the relay student's gain over the 0-byte student should concentrate on those steps.
  Its agreement with the teacher rises most where the 0-byte student disagrees with the teacher.
- The "phase that measures nothing" is the regime where the 0-byte student is enough: heavy load (h6, L-156), where
  messages add ≈ 0 on seed 1.

## MASTER (the price of a calibration query; ledger 01_MASTER A–F = the cross-chain synthesis)

**What it proves:**
- a necessity dichotomy: without the calibration query type the value is EXACTLY 0 on indistinguishable worlds;
- an exact square-root price law;
- anchor necessity on one instance.

**The ledger:**
- cross-chain synthesis and process rules;
- novelty collisions named for every chain;
- "the bottleneck is novelty, not sample size";
- MASTER's own gap: the certificate contract's soundness was supplied, not derived;
- a kept negative: certification is slower than exact solution at small size.

**Validation of L-167 (e)** ("MASTER: a regret floor for the no-evidence policy plus a priced acquisition law, frame for
the 0-byte student"):
- LOOSE.  MASTER has no regret floor for a no-evidence policy.  It has a dichotomy (value 0 without the missing type).
- The floor for 0-byte policies is UNIFIED's `randomised error floor 1/|H|` and Paper B's zero-query floor.
- MASTER's contribution to the story is the NECESSITY half: some decisions are impossible without the neighbour's
  information, whatever the local sampling.

---------------------------------------------------------------------------------------------------------------------

## Validation table of the parallel session's L-167 (a)–(g)

| item | L-167 claim | verdict | why |
|---|---|---|---|
| (a) Paper C | one order serving every capacity; a worst-capacity regret theorem RLM lacks; the regret collapses with relay | **structure right, theorem does not transfer, collapse trivial** | exact frontiers are for g_m (one signed value vector); E3 has per-receiver value vectors; "collapse" = all subsets equivalent when every packet is complete and fresh (true by definition, not by C's theorems); the real E3 effect is dynamic (ages) |
| (b) ADAPTIVE | age-first = greedy most-deficient tracking; with K_i ≥ 1 it bounds every sender's head-gap; deficit ≤ 1 | **mis-sourced** | ADAPTIVE PROVES the greedy online rule violates deficit ≤ 1 (26/23 witness; up to ≈ 2); `tracking_bound`/`tracking_exists` are per-horizon, non-online; uniform-target round-robin is elementary; the E3 age bound must be proved for the prefix/relay dynamics directly |
| (c) FUNCTIONAL lifetime | margin > 2L(κ + H ν) ⇒ relay action = fresh action | **valid in structure; constants empirical** | LIFE2/LIFE3 apply to any score function; δ, ν, L are unmeasured; test predictively (V-F) |
| (d) `current_step_invariance_insufficient` | the stale-cache obstruction, repaired by relay with ages | **valid** (it is a MARL module; a formal witness that current-step checks miss future flips) | it is a witness, not a quantitative law |
| (e) MASTER | regret floor for the no-evidence policy, frame for the 0-byte student | **loose** | the floor is UNIFIED / Paper B; MASTER gives necessity (value 0 without the missing type) |
| (f) SUPPORT / N5 | decide without identifying justifies 2–3 B | **valid as framing; must be whole-fibre** | Paper B's safe-order law + SUPPORT's fibre condition; measurable (V-B) |
| (g) STRUCTURAL | relay collapses the needed number of streams to 1; cite Bienkowski 2026 | **valid as a testable prediction** | the monotone/signed regime split; the tolerance collapse; incremental-optimisation prior art is already in the chain's own notes (V-S) |

## What is genuinely new that L-167 missed (to strengthen the paper)

1. **Paper A's starvation theorem is the congestion order.**
   - The cached-queue ranking is a frozen surrogate.  At low capacity its optimal (greedy) order gives ZERO injection to
     the low-ranked senders, hence zero coverage (46 % of pairs at cap4 in the simulator).
   - The rotation is the repair.  The repair frontier's shape ("no threshold, linear") is testable by a β-mixture order
     (V-A).
   - This turns "rotation helps at low capacity" from an engineering fix into an instance of a proved phenomenon.
2. **Paper C's band = the rotation's fairness; ADAPTIVE's quota = its dynamics.**  Paper C's own novelty brief lists
   house-monotone apportionment (Balinski–Young: one sequence serves every house size within quota) as its closest
   analogue.  Over time, the E3 scheduler IS an apportionment of head positions.
   - With uniform targets the largest-deficit rule is round-robin and bounded.
   - With decision-weighted targets (important senders more often), ADAPTIVE's census predicts that the natural rule
     overshoots (deficit up to ≈ 2) while the quota method does not (V-Q).
3. **The value of communication = obstructions inside local fibres** (UNIFIED, Paper B, SUPPORT).  This gives the
   0-byte-student bar a theory: the student is the best rule on the fibres, and messages must beat it exactly where an
   obstruction hides (V-U).
4. **The budget-frontier regime split (STRUCTURAL):** signed (stale/flat, non-monotone, needs menus) against monotone
   (fresh/relay, one order suffices).  E3 already contains a non-monotone frontier (L-119) (V-S).
5. **The decision-lifetime certificate (FUNCTIONAL + D6 + the MARL module)** links age to decision agreement, and hence
   explains why the rotation matters and where saturating ages at 14 steps is harmless (V-F).
6. **Process lessons that apply to our claims:** paired comparisons; one policy, not a class; "not free"; read the
   theorem, not the corollary; satisfiability witnesses; companion status records.

## Direct verification experiments (to implement; each tests a stated prediction, not a transferred theorem)

| id | source | prediction | measurement | cost |
|---|---|---|---|---|
| V-A | Paper A starvation + repair | coverage of starved senders rises from 0 with NO threshold as β grows; low-capacity waiting improves already at small β; iid cost grows with β | β-mixed order (rotation w.p. β, cached-queue otherwise), β ∈ {0, .05, .1, .25, .5, 1}; information level (exact ages and coverage) in the traffic-free simulator and via AgeMirror in CityFlow; waiting on the development panel | simulator: seconds; CityFlow: 2 seeds × 3 conditions × 6 β eval-only |
| V-Q | ADAPTIVE quota / Paper C band | uniform targets: agefirst deficit ≤ 1 and head-gap bounded, prefix unbounded; weighted targets: largest-deficit overshoots 1 on some weights, the quota method never | E3 scheduling simulator with real capacity processes; ADAPTIVE's witness weights; census over random targets | seconds |
| V-F | FUNCTIONAL lifetime + D6/MARL margin | predictive certificate (δ, ν from TRAIN) is sound on held-out steps; agreement rises with margin and falls with age; rotation raises the certified share | per receiver-step: the relay student's logits on its relay view vs on the counterfactual fresh full view; ages; margins | eval-only probe |
| V-U | UNIFIED floor / Paper B / SUPPORT | the relay student's advantage concentrates where the 0-byte student disagrees with the teacher | the same probe records teacher (full raw), 0-byte student, relay student actions on the same states | same probe |
| V-B | Paper B safe order / SUPPORT fibre | the 3 B code resolves the teacher's obstructions: teacher(raw) vs teacher(3 B) disagreement is low and concentrated at small margins | same probe (teacher on raw full vs quantised full) | same probe |
| V-S | STRUCTURAL regime split | the budget frontier (waiting vs K = 1..7, fixed capacity) is non-monotone for stale-kept or flat actors and monotone for relay; relay menus gain nothing | eval with capacity `fixedK` for K = 1..7 | eval-only, 7 K × actors |

---------------------------------------------------------------------------------------------------------------------

## Results so far (15:3x)

### Traffic-free (`scripts/MARL_e3_theory_sim.py`, 300 episodes; ADAPTIVE's witness is a built-in self-check)

**V-Q, ADAPTIVE reproduced on the E3 apportionment:**
- the witness gives 26/23 at t = 11 and 31/23 at t = 14;
- census over 2000 random targets: largest-deficit violates unit quota on 209 targets (worst 3/2); the Balinski–Young
  quota method violates it on 0 (worst 62/63);
- uniform targets: both rules stay ≤ 8/9;
- the sticky (frozen) order leaves some senders never at the head over 26 steps.
- **Defect found in the ADAPTIVE paper:** the trace caption says the maximum is unique at every step, but ties occur at
  t = 0, 4 and 7.  All 18 tie-break paths still reach 26/23, so the theorem is right and the caption is wrong.

**V-A, Paper A's starvation and repair, information level:**
- Coverage has NO THRESHOLD in β.  At low capacity (K ~ U{1..3}), never-covered pairs go 0.41 → 0.27 at β = 0.02 →
  0.15 at β = 0.05 → 0 at β = 0.25.
- The mean age is NOT monotone: 1.86 → 3.26 at β = 0.1, then 1.40 at β = 1.  Small β brings starved senders in as
  STALE copies.
- So at decision level, "no threshold" needs the student to use stale copies at least as well as absence.  That is an
  open empirical question (V-A closed loop).

**V-S, raw vs relay packets under const K:**
- Relay dominates raw packets in coverage at every K.
- A PATHOLOGY: raw packets + rotation with id tie-breaks at K = 2 phase-lock.  The paid triples rotate together, so
  25 % of pairs are never covered.  Relay removes it (coverage 0.979).
- Music reading: a hocket whose voices lock in phase.  The fix is a coprime or randomised rotation, a
  maximally-even / Euclidean schedule.  This is the ADAPTIVE lesson that tie-breaking in an apportionment rule matters.

### Probe smoke (`scripts/MARL_e3_theory_probe.py`, relay_st_s0, agefirst, iid, 4 episodes; all self-checks pass)

**V-F:**
- identity violations: 0;
- agreement of the relay action with the fresh-full action rises with the fresh gap: 0.62 / 0.89 / 0.97 / 0.98 / 1.00
  by quintile;
- a q99 upper-envelope certificate is sound (1.0) but covers only 9 % of the held-out steps.  The fitted δ is large
  (logit scale): the lifetime certificate is valid but conservative, the same shape as the loose IBP certificate of
  L-94.

**V-U:**
- the 0-byte student disagrees with the teacher on 15 % of receiver-steps;
- there, the relay student agrees with the teacher on 63 % (with a fresh full input, 74 %);
- where the 0-byte student agrees with the teacher, the relay student agrees on 93 %;
- net: +3.4 points of teacher agreement for relay over the 0-byte student.  The gain sits in the split where local
  information does not resolve the decision, and relay pays a little where it does.

**V-B:**
- the teacher's decision changes under 3 B compression on 1.6 % of steps;
- all of it falls in the smallest raw-gap quintile (8 %; 0 elsewhere);
- so the 3 B code resolves every obstruction except near-ties.  That is D6's 2δ margin shape and Paper B's "decide, not
  identify", measured.

## Full-panel probe, agefirst order (6 runs: 2 seeds × iid / cap4 / low; parity 128/128 each; 0 identity violations)

| run | relay = fresh action | agreement by fresh-gap quintile | agreement by max age | 0B ≠ T share | relay = T where 0B ≠ T | relay = T where 0B = T | T(3 B) ≠ T(raw) |
|---|---|---|---|---|---|---|---|
| s0 iid | 0.891 | 0.64 … 1.00 | age 1 .90, 2 .86, 3 .83, 4 .70 | 0.144 | 0.628 | 0.935 | 0.021 (0.103 in lowest-gap quintile) |
| s0 cap4 | 0.870 | 0.59 … 1.00 | 1 .90, 2 .86, 3 .86 | 0.144 | 0.590 | 0.934 | 0.023 |
| s0 low | 0.844 | 0.56 … 0.99 | 1 .94, 2 .87, 3 .83, 4 .81, 5 .80, 6 .78 | 0.150 | 0.530 | 0.922 | 0.022 |
| s1 iid | 0.891 | 0.63 … 1.00 | 1 .90, 2 .86, 3 .82 | 0.164 | 0.704 | 0.939 | 0.013 |
| s1 cap4 | 0.875 | 0.60 … 1.00 | 1 .93, 2 .86, 3 .84 | 0.166 | 0.672 | 0.939 | 0.014 |
| s1 low | 0.859 | 0.59 … 1.00 | 1 .99, 2 .87, 3 .84, 4 .84, 5 .83 | 0.168 | 0.640 | 0.930 | 0.013 |

**Certificate:**
- Fitted on traffic seeds 901–932, tested on 933–964, quantile q of osc(L_relay − L_fresh) per age.
- It is SOUND at every q (≥ 0.9997), and its coverage is 0–23 %.
- Coverage is lowest at low capacity, where the ages are longest.

**Readings:**
- **V-F:** the mechanism is there.  Agreement with fresh complete information rises with the decision margin and falls
  with the relay age, as LIFE2/LIFE3 predict.  A worst-case lifetime certificate is valid but covers few decisions
  (δ ≈ 22–49 logits).
- **V-U:** consistent on 6/6 runs.  The relay gain over the 0-byte student comes from the steps where local information
  does not settle the teacher's decision.
- **V-B:** consistent on 6/6.  3 B compression changes the teacher's decision on 1.3–2.3 % of steps, almost all in the
  smallest-margin quintile.

---------------------------------------------------------------------------------------------------------------------

## Proposed paper narrative v2: "the stronger direction" (to be confirmed by V-A / V-S; fallback = the analysis paper)

**Thesis.**  One broadcast stream decoded as a prefix by receivers with unknown, unequal budgets is an INFORMATION-DESIGN
problem with four classical failure modes.  Each has a theorem in the old corpus, each appears in the E3 failures, and
each has a repair that the experiments verify.

| failure (E3 evidence, kept as story) | theorem shape (source) | repair | direct check |
|---|---|---|---|
| messages make learned actors worse than silence; non-monotone budget frontier (L-105, L-119) | signed cancellation: one schedule cannot serve every budget (STRUCTURAL) | complete packets (relay) → monotone regime → one order suffices | V-S (running) |
| the congestion order never injects low-ranked senders at low capacity (46 % never covered) | frozen-surrogate STARVATION, linear repair (Paper A) | rotate the head; β-mixture | V-A (information: no threshold; closed loop running) |
| deterministic rotation can phase-lock (raw packets, K = 2) | quota / apportionment tie-breaking (ADAPTIVE; C's band) | relay, or a quota / maximally-even rule | V-Q (reproduced ADAPTIVE; lock found) |
| stale copies change decisions (FO, stale-kept cliff L-125) | decision lifetime: margin > 2(δ + hν) (FUNCTIONAL LIFE, D6 2δ, MARL argmax_stable) | ages in the packet, rotation to bound h | V-F (agreement rises with margin, falls with age) |
| raw 25 B payloads | decide ≪ identify; the safe-order law (Paper B, SUPPORT, N5) | 3 B decision summaries | V-B (1.3–2.3 % flips, at near-ties only) |
| "communication gain" that is only training-time (FO, set_fresh, FO-student vs the student) | obstruction floor 1/\|H\| inside local fibres (UNIFIED, Paper B) | measure against the distilled 0-byte student; C1 and dose-response controls | V-U (gain sits where 0B ≠ teacher) |
| MP2 harmed by its own messages | reference calibration (MASTER) | maxq | L-114 |

**Why it is more interesting than "relay + distillation":**
- The contribution becomes a MECHANISTIC account of when broadcast messaging helps.  Each mechanism is tied to a
  theorem shape and a falsifiable prediction, and the fixes fall out of the account rather than being engineered.
- The pre-registered positive result (L-175) is the payoff.
- The failures are the evidence that the mechanisms are real: selectors, flat actors, FO, set_fresh, relay without
  rotation, relay_ppo, and bass ≡ agefirst.

**Honest novelty boundary:**
- The mechanisms are known in their home fields: incremental optimisation / RLM / PET; AoI and apportionment;
  approximate modularity; decision-region determination; CTDE distillation.  Relay itself has prior art (Gama et al.,
  NeurComm).
- New are: the channel model in MARL; the assembly into one account with direct checks; the distilled-silence bar with
  controls; the phase-lock observation; and the measured decision-lifetime curves.
- None of the corpus theorems is claimed to hold for E3 (L-86).  They supply the SHAPE, and E3 supplies the
  measurement.

**Needed before this can be the paper:**
- V-A and V-S closed-loop results;
- more seeds;
- a Lean module (paused by the user) for the E3-specific statements, if the authors want theorem-level claims: the age
  bound under prefix decoding plus relay with K_i ≥ 1; the lifetime composite; monotonicity under complete fresh
  packets.

---------------------------------------------------------------------------------------------------------------------

## Novelty against "it is just relay + distillation" (16:2x, 30/09; user 16:1x: "with 10–11 papers, is there really nothing?")

Written BEFORE the new runs below, so that the reasoning is not lost.  Each item says what the corpus supplies, what the
E3 evidence is, and whether it is a new CLAIM, a new METHOD element, or only framing.

### A. The strongest answer is already in our data: relay + distillation is NOT sufficient on this channel
- Pre-registered panel 2601–2664 (L-175), secondary rows: relay + distillation under the natural (congestion-ranked) order,
  seed 0, is WORSE than the zero-byte bar at low capacity, +0.96 % [+0.10, +1.88], and not better at cap4, +0.68 %
  [−0.12, +1.50].  Seed 1 passes (−1.76 / −1.74 %).  Development panel: +0.9 / +0.4 % (seed 0).
- What makes it work is a SCHEDULING property of the stream head (rotation), and Paper A's frozen-surrogate starvation
  says why: the congestion ranking is the optimum of a frozen surrogate and gives zero head mass to low-ranked senders.
- So the paper's claim is "relay + distillation fails where the theory says it must, and the theory's repair fixes it",
  not "relay + distillation works".  Prior relay work (Gama et al., NeurComm, TEM, AC2C, ExpoComm) has no committed prefix
  stream, so it has no head, no starvation, and cannot see this failure.  This must be in the abstract and introduction.

### B. A method element that relay + distillation does not contain: a lifetime-deadline head (Paper A + FUNCTIONAL + pinwheel)
- Paper A: the repair should be TARGETED at the starved cells.  A uniform β-mixture (V-A) is the untargeted version, and
  seed 1 shows it is inefficient (flat until β ≥ 0.5 at cap4).
- FUNCTIONAL LIFE4: a copy has a certified decision lifetime H*.  Refresh a sender when its copy is about to expire.
- Rule "deadline<D>": keep the congestion ranking (best at iid), but promote to the head every sender whose worst relayed
  age over the receivers (AgeMirror, scheduler information only) is ≥ D steps, oldest first.  D = ∞ is the prefix order.
- Prediction: prefix-level iid waiting and rotation-level low-capacity waiting, so it dominates both orders.
  Eval-only, development first (D ∈ {2, 3, 4}), then a pre-registered panel only if it dominates.
- **Pinwheel scheduling** (Holte et al. 1989; density threshold 5/6 proved by Kawamura, STOC 2024; TO VERIFY): "every
  sender j must be at the head at least once every a_j steps" is EXACTLY a pinwheel instance.
  - The head is decoded by every receiver when K_i ≥ 1, so an a_j-pinwheel schedule bounds j's age at every receiver
    by a_j − 1.
  - With a_j = the certified lifetime H*_j, density Σ_j 1/H*_j ≤ 5/6 guarantees one committed order that keeps every
    copy within its lifetime at every receiver and every capacity.
  - Composed with LIFE2/LIFE3 (margin > 2(δ + hν)), every margin-certified decision then equals the fresh decision.
  - This is a real theorem SHAPE for the channel: a known theorem plus a head-reach lemma.  The lemma is Lean-easy; the
    pinwheel theorem would be cited, not re-proved.
  - The deadline rule is an online EDF heuristic for that pinwheel instance.
- Related prior art to cite if used: broadcast disks (Acharya, Alonso, Franklin, Zdonik, SIGMOD 1995), which schedule one
  broadcast for clients with different needs, and pinwheel.
- Music link (the user's 13:1x request): maximally even rhythms (Euclidean / Bjorklund, Toussaint 2005) are the
  deterministic fix of the phase-lock (V-Q); pinwheel is a polyrhythm with deadlines.

### C. Head-reach lemma and a bound (elementary, provable, not yet in Lean)
- With K_i ≥ 1 for all i, the head is decoded by all m − 1 other receivers, so the age of j at any receiver is at most
  the time since j was last at the head.  This holds for raw and relay packets alike.
- Under agefirst (oldest last-paid first), a sender's rank strictly decreases every step it is not paid.  The head is
  always paid and moves behind it, and a newly paid sender is newer than it.  So every sender reaches the head within
  m − 1 steps, and every age is at most m − 1 = 8 steps, for ANY capacity sequence with K_i ≥ 1.
- The sticky congestion order has no such bound (starvation).
- Relay adds INDIRECT refresh: the head carries its whole table, so j's age at everybody is at most j's age in the
  head's table.  That is why measured mean ages are 0.8–1.4, far below 8.
- Phase-lock (V-Q) explained exactly:
  - with raw packets at constant K = 2, the paid prefix is 3 packets, and deterministic agefirst rotates fixed
    triples;
  - the third member of a triple is decoded only inside its triple;
  - so each receiver misses 2 of 8 senders forever, which is the 25 %;
  - relay fills it, because the triple's head carries the third member.

### D. AUDIT CORRECTION of my own V-U claim (must go into the paper)
- V-U splits receiver-steps by whether the zero-byte student agrees with the teacher.  On the "agrees" split the
  zero-byte student is right by construction, and on the "disagrees" split it is wrong by construction.  So "relay's
  teacher-agreement advantage sits in the disagreement split" is TRUE BY CONSTRUCTION for ANY other policy: a
  tautology, not evidence.
- The numbers themselves are fine: relay recovers 53–70 % there and loses 6–8 % elsewhere.
- The informative quantity: relay's recovery rate on that split MINUS the recovery rate of a SECOND imitator with the
  same local information (a second zero-byte student from the same teacher, different seed).
  - If both students fail on the same steps (true obstructions of the local fibre), the null recovery is low and relay's
    excess is message value.
  - If the first student's errors are training noise, the null recovers them too.
- Launched 16:20: `scripts/RUN_marl_e3_zero_replicate.sh` (distill_none_rep_s0/s1, seed 100 + s, same command
  otherwise).  The probe is then re-run with --zero = the replicate on the same states (the rollouts are the relay
  student's, so records align; check it).
- Lesson (general): conditioning on one model's error and then showing another model is better there proves nothing
  without a same-information null.

### E. Further caveats found on re-reading the probe numbers
- **V-F.** Agreement falls with the maximum relayed age under agefirst (0.94 → 0.78 at low capacity).  Under the
  prefix order the curve is NOT monotone (e.g. s0 prefix iid: 0.92, 0.90, 0.91, 0.88, 0.92, 0.84, 0.92 for ages 1–7).
  The maximum over agents includes starved, possibly irrelevant, senders.  Report it that way; an age weighted by
  relevance would be the right variable.
- **V-B.** Flips at near-ties are what any small input perturbation does to an argmax.  It is consistent with "decide,
  not identify", but weak as evidence for Paper B.
- **V-A.** Seed 0 at cap4 is concave (−0.96, −2.39, −2.86, −3.33, −3.17 % at β = .05 … 1).  Seed 1 is convex (−0.31,
  −0.44, −0.61, −1.45, −2.57 %).  Seed 1's iid cost is significant at β = 0.1 and 0.25 (+0.85 % [+0.13, +1.58],
  +0.99 % [+0.21, +1.80]).  "No threshold" holds for seed 0 only.
- **V-U cross-condition.** Across the 12 probe runs, the net teacher agreement (relay minus the zero-byte student)
  tracks the waiting gain against it:
  - s0 prefix cap4 −0.021 → +0.94 %; s0 prefix low −0.028 → +0.35 %;
  - s1 agefirst cap4 +0.061 → −4.14 %.
  - This is a predictor, not a mechanism: agreement with a better teacher is expected to track waiting.

### F. What the corpus does NOT give (do not force it)
- MASTER and QUERY: nothing beyond framing, and the MASTER "floor" is mis-sourced (it is UNIFIED / Paper B).
- Paper C's exact frontiers: they are for one signed value vector.  The "price of one ordering" needs a per-receiver menu
  oracle; L-128 (a) found orders under FO within −0.3 … −0.6 %, CIs containing 0, so there is little to show.
- ADAPTIVE: its theorems are about the FAILURE of greedy tracking with non-uniform targets.  Uniform rotation is
  elementary.

### G. Ranked plan (what actually strengthens the paper)
1. Put A in the abstract and introduction (no new run needed).
2. Test B (deadline head) today, eval-only; if it dominates, pre-register it.
3. State C as a proposition with proof sketch, labelled "Lean pending".
4. Replace the V-U inference by the replicate null (D).
5. Figures for V-A, V-S, V-F, V-U and the pre-registered result; verify every bibliography entry.

---------------------------------------------------------------------------------------------------------------------

## Re-read of paper_marl.tex (v1) and paper_marl_v2.tex: where the novelty can be raised (16:4x, 30/09; user 16:3x)

Also re-read for this section: the D6 ledger's "cyclic design is optimal in its class" (05_D6 K, §159–162).
- It is optimal among fixed linear A-invariant statistics of legal queries, under Gaussian noise.
- It maps to the rotating head only as "balanced designs are classical".
- WEAK lever; do not use beyond one sentence.

### v1 assets that v2 does not use yet (the most important finding of this re-read)
1. **v1's PROVED commitment theory explains why v2 needs no selector.**
   - Theorem T1 (deployable regret) and the block frontier (`LeanMarlBlockFrontierV1`) bound the price of committing one
     order by 2η·Σ_b(|P_b∖T_b| − R)_+, where η is the ScoreLocal constant (how far the marginal values are from a score).
   - E1b's uniform-score result (`LeanMarlE1bUniformV1`) shows a UNIFORM score can satisfy ScoreLocal without knowing
     the interaction.
   - With relay packets every packet carries every agent's copy, so packets are near-SUBSTITUTES.  Each receiver's value
     of a decoded set depends mainly on how many packets it gets and how fresh their tables are, not on whose they are.
   - So η for the uniform score should be SMALL under relay.  Every order is then top-k by that score, and the proved
     frontier gives a small commitment price for ANY order.  What is left is the age dynamics, which is exactly what
     rotation controls.
   - This turns L-167 (a)'s "collapse" from a triviality into a QUANTITATIVE, PROVED bound whose constant is
     measurable.
   - **Direct test (new, V-η):**
     - re-run v1's reduced bridge panel (`scripts/MARL_e3_bridge_panel_v2.py`: 16 states, one receiver, all 256 decodable
       sets, continuation value f, the LPs for η* and η_top) on the RELAY student, and compare with the raw-packet actor's
       η_top (median 7.0 / 6.0 against an f-spread of 9.6 / 8.5, v1);
     - prediction: η_top(relay) ≪ η_top(raw), and the geometric loss at R = 0 is ≈ 0;
     - cost: a port of the bridge panel to the relay merge (engineering, a few hours), then rollouts.
2. **v1's failures become the control arm of v2's claim.**
   - v1: selection on raw packets does not beat the prefix (critic ranking loss +15, commitment geometry only 0.3–0.8).
   - v2: representation (relay) plus scheduling (rotation) beats the bar.
   - Together: "the lever is WHAT a packet carries and WHEN the head rotates, not WHICH packets are chosen".  v2's
     appendix states the history but does not make this argument.
3. **v1's SafeEdit theorem (edit only if the estimated gain exceeds 2ε)** applies to ANY order edit, including the
   deadline promotion.  It is not needed unless the deadline rule uses estimates.
4. **v1's receiver bid (1 B) plus L-128 (d)** (the receiver's own no-message margin predicts message-induced action
   change, AUC 0.73; the 50 % lowest-margin steps hold 72 % of the changes) suggest a decision-aware head.
   - Receivers bid their margin, and the head goes to the sender most needed by fragile receivers.
   - It is a synthesis of v1 and v2, but bass ≡ agefirst suggests the head's identity matters little once rotation
     exists.  LOW priority; test only if the deadline head shows the head choice matters.

### v2 text: concrete novelty edits (no new run needed unless marked)
- **Abstract and introduction:** lead with the pre-registered failure of relay + distillation at low capacity
  (seed 0, +0.96 % [+0.10, +1.88]).  Rotation is required, and Paper A's starvation is the reason.  The current
  abstract says "each missing piece breaks it" but hides that the prior-art combination itself fails.
- **Contributions:** add (v) the head-reach lemma and bound, with the phase-lock witness; (vi) the commitment bound from
  v1 instantiated by measurement (V-η, if run); (vii) the deadline/pinwheel head (if the development test passes).
- **Part II:**
  - relabel M1–M5 by the V-ids and add figures;
  - correct V-U (tautology; the replicate null);
  - state V-F's prefix-order non-monotonicity;
  - state V-A's seed-dependent shape;
  - add V-Q as its own paragraph.
- **Related work, to add after research:** AoI in gossip networks (the relay merge is timestamped gossip), pinwheel
  scheduling and broadcast disks (the head schedule), the "age of incorrect information" or value-of-information line
  (the decision lifetime), and CTDS-style no-communication students (the bar).
- **Title:** the current title puts the bar first.  An alternative that names the channel and the mechanism:
  "Why relay needs rotation: prefix-broadcast communication against a distilled zero-byte bar".  The authors decide.

### Research to do now (collision checks for the new elements)
- R1: gossip/AoI with timestamped relays, "age of gossip", version age, multi-hop broadcast AoI.  This is the likely
  prior art for the relay-age dynamics.
- R2: pinwheel (the Kawamura 5/6 proof), pinwheel ↔ AoI, broadcast disks.  This is prior art for the deadline head.
- R3: MARL with timestamps/ages in messages, delayed or stale communication, AoI-aware MARL communication.
- R4: evaluation of learned communication against a distilled no-communication student (collision risk for the bar).
- R5: prefix or layered decoding with heterogeneous receivers in MARL (re-check that it is still absent).

---------------------------------------------------------------------------------------------------------------------

## 19:0x update: results, corrections, the user's block-frontier question, the pasted review, heavy runs

### CORRECTION of item C above ("head-reach lemma and a bound"): the age bound was WRONG
- What is true (rank argument, checked by simulation): under age-first with K_i ≥ 1, every sender is TRANSMITTED
  (decoded by at least one receiver) at least once in every m consecutive steps.  Measured longest untransmitted run:
  2 (iid, cap4), 3 (low), 4 (constant K = 1) steps.
- What is false: "every sender reaches the head every m steps, so every age ≤ m − 1".
  - A sender can be transmitted at a non-head position, which resets its rank.
  - With index tie-breaks the head concentrates: under iid, senders 6–8 take 80 % of head slots, and about 3 of 9
    senders never reach the head in 26 steps.
- So age-first rotates the TRANSMITTED SET, and relay carries fresh copies through whoever holds the head.  An age bound
  at every receiver needs more hypotheses; it is not proved.
- Fixed in paper_marl_v2.tex (Claim 1 is now an injection bound; Claim 3 uses the measured age) and in memory.
- The pasted review's T1 ("fair head + K_i ≥ 1 ⇒ bounded age; E[H_β] = O(m/β)") has the same gap.  Under mixing, a
  sender transmitted at a non-head position is not decoded by every receiver.

### Results of this round (ledger L-178, L-179)
- **V-U with a same-information null: SURVIVES.** Excess recovery +0.19 … +0.34 (12/12 runs, CIs > +0.16).
- **The bar varies with the student's seed:** Z′ vs Z is −0.26 % (s0) and −1.20 % (s1, significant).
  - Relay + rotation vs Z′ still wins 6/6.
  - Relay without rotation vs Z′ fails or ties in 4/4 low-capacity cells.
  - This STRENGTHENS "relay + distillation is not enough".
- **Deadline head: NEGATIVE** (does not dominate for any D).
- **relay6Cage seeds 4/5:** s4 strong (−3.1 / −3.2 / −1.9 %); s5 weak (−0.8 / −0.9 / −0.8 %), and s5's teacher has no
  headroom over compiled silence (BYTEBUDGET vs 0B +0.6 %).
- **Pre-result prediction for s6–s9 (L-179):** the relay gain tracks the teacher's headroom over compiled silence.

### Answer to the user's question (19:0x): can v1's block-frontier bound fix things?  Does it solve v1's problem?
- It does NOT rescue v1's METHOD.  v1's problem was not an expensive commitment.
  - On raw packets the geometric loss at R = 1 was already small (0.3–0.8).  The loss was the critic's ranking, the actors
    lost to silence, and the oracle headroom was action perturbation.
  - The bound predicts the opposite of "selectors help": if η is small under relay, ANY committed order is near-optimal,
    so there is nothing for a selector to gain.
- What it CAN do for v2: turn v1's proved theorems into a certificate.
  - "Under relay, committing one order costs at most 2η(k − R)_+, with η measured" explains why v2 needs no selector
    and why only the head timing matters.
  - That links v1 and v2 into one story: v1 proved when commitment is cheap; v2 shows relay makes it cheap and moves
    the problem to freshness.
- Required measurement (V-η, not run): port `scripts/MARL_e3_bridge_panel_v2.py` to the relay merge.  Measure η* and
  η_top, plus the value of R = 1 revisions and direct selection, on the relay student.  Light compute (v1: ~11 min per
  actor for 16 states); a few hours of porting.
- Either outcome is informative.
  - η small: the certificate holds.
  - η large or R = 1 still gains: v1's selector line reopens on relay packets.  The pasted review's "post-reveal patches
    that promote stale sources" is that variant, but the deadline-head result makes it unlikely to pay.

### The pasted literature review (another worker, 19:0x): verified vs not
- VERIFIED to exist, with the claimed content (search 18:3x–19:0x):
  - Chauhan & Bera 2026 (arXiv 2609.34373);
  - CAIC (UAI 2026, PMLR 337; "stale messages under delay can be worse than none");
  - VIL2C (AAAI 2026, arXiv 2511.19146);
  - CoDe (AAAI 2025, arXiv 2501.05207);
  - DACOM (AAAI 2023);
  - FCMNet (AAMAS 2022, arXiv 2201.11994);
  - LMAC (ICML 2026, arXiv 2605.18077);
  - CACOM (AAMAS 2024, arXiv 2312.15600);
  - I2C (NeurIPS 2020);
  - HINT (RSS 2026);
  - CoDiMAD (arXiv 2607.09587);
  - CTDS, PTDE, TEM, AC2C, ExpoComm, UniComm, RLM, PET.
- CORRECTED: the "2026 fair-scheduling AoI paper" is Jien & Kuo, ALGOWIN 2023, LNCS 14061.
- NOT verified, so not cited: QRC-TSC; the "2025 traffic-signal information-sharing" paper; CMVC; MUTE's bound; M2I2's
  "dimensional importance" details (M2I2 is cited in v1 only).
- AGREE, and applied in v2:
  - the component-level collisions;
  - the title change;
  - "compiled silence as an audit principle";
  - "coverage alone is insufficient, fresh decision-relevant coverage";
  - the V-S reframing (freshness monotone, control not);
  - the V-A reframing (coverage vs fresh coverage);
  - the CTDS/PTDE distinction paragraph;
  - the prefix-channel wording;
  - the limitations (m = 9, O(m) table, zero delay).
- DISAGREE or qualify:
  - its T1 age bound (above);
  - its claim that V-U "shows the benefit exactly where the zero-byte student lacks information" needed the replicate
    null, which is now done;
  - "at least 5 training seeds": 10 teachers and 10 relay6Cage students exist, and s8/s9 finish today.  What is missing
    is their evaluation plus a second pre-registered panel, not training.

### Heavy runs to hand over (the user's other machine)
1. **Second road network with m ≤ 9**, so that the 185-bit relay packet still fits 25 B.  For example a 2×4 grid or a
   1×6 arterial.  For m ≥ 10 the table does not fit (m = 10: 206 bits > 200), and a truncation rule (nearest or oldest
   k agents) is an author decision.  Per network: scenario generation; teachers set_full ×5 seeds; set_none ×5;
   zero-byte students ×5 (+ replicates); relay students ×5; then the grid.  This is the heaviest item.
2. **Second pre-registered panel for 10 seeds** (relay6Cage s0–s9 + age-first vs the zero-byte students, and vs the
   replicates where they exist): evaluation only, 10 × 3 conditions ≈ 30 evaluations.  The protocol must be written
   first.
3. **Replicate zero-byte students for seeds 2–9** (8 trainings, about 70 min each at load): this makes the bar
   two-student everywhere.
4. **Reserved test 1301–1316, once, after a freeze.**  Light compute, but an author decision.
5. **A delay sweep (0 / 1 / 2 steps).**  Needs a small evaluator change (a delayed relay merge); light compute.
6. **V-η (bridge panel on relay).**  Light compute, engineering first.
7. **Whole-fibre obstruction test.**  Needs a probe that records the receiver's own local features, then binning.
   Light.
