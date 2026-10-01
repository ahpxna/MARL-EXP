# A new MARL paper from the existing CIG-AMF results

Research/design memo, 2026-09-26. Written incrementally at the user's request. This is a proposed research package, not a claim that the old experiments establish the new algorithm.

## Decision 1: a synthesis is possible, but the unit of contribution must change

Do not combine ten abstracts into one paper. Define one cooperative control problem with limited and varying information/computation, one executable algorithm, and one closed-loop evaluation. Use the old results as the mathematical ingredients that are actually instantiated.

The historical code already has a concrete MARL path: `scripts/run_paper_b_allocation.py` selects an explicit neighbour core and uses a policy/value network, with baselines `C-Core`, `AbsD-Core`, `Random-Core`, `Correlation-Core`, `Attention-Core`, `Oracle-C-Core`, and `Full-Explicit`. Its old “Paper-B” naming refers to an earlier allocation project, not today's obstruction-order manuscript. The code must be audited and renamed in an adapter rather than silently relabeled.

Historical smoke runs in `research/new_chains_v2/ACTUAL_EXPERIMENT_RUN_CHECK.md` establish that some episode pipelines executed, while explicitly failing scientific gates or missing learned adapters. They do not establish a competitive trained MARL result. The 2026-09-07 six-paper plan explicitly separated structural theory completion from deep MARL; that explains part of the drift toward standalone theory.

Recommended research question, pending the detailed bridge below:

> Under changing resource budgets, which interaction information is sufficient for a team to retain its control decisions, and how much coordination loss can a small revision of the selected interaction structure recover?

Use learned multi-agent policies and moving traffic. Forecasting may be one useful feature or auxiliary task, but is not the entire MARL application.

## Decision 2: known literature blocks the generic claim

Primary sources checked:

- SchedNet, ICLR 2019: https://openreview.net/pdf?id=HUAnBToP_a . Learned scheduling of who communicates under restricted shared bandwidth.
- NDQ, ICLR 2020: https://openreview.net/pdf?id=HJx-3grYDB . Communication minimization tied to action-relevant value functions; generic decision-relevant communication is not new.
- IMAC, ICML 2020: https://proceedings.mlr.press/v119/wang20i.html . Informative compact messages and scheduling under bandwidth constraints.
- ETCNet: https://arxiv.org/abs/2010.04978 . Event-triggered communication under bandwidth constraints; “communicate only when needed” is already a prior claim.

Thus the candidate distinction must be the combination of a precise decision-sufficiency object, non-nested budget optima, limited repair, and a control-level analysis/evaluation. This is a candidate distinction to test against closer dynamic graph and value-of-communication papers, not a priority claim.

## Decision 3: the closest collisions change the proposed headline

The following primary sources were read beyond a title/abstract where indicated.

| Prior work | Concrete overlap | Consequence for our proposal |
|---|---|---|
| [Zhang–Lesser, AAMAS 2013](https://people.csail.mit.edu/chongjie/pub/zhang-aamas13.pdf), Definition 2 / Algorithm 2 | Defines potential loss from not coordinating with a subgroup, then selects a coordination set subject to a loss threshold. | Neither selecting beneficial neighbours nor a set-level loss objective is new by itself. |
| [CASEC, ICLR 2022](https://arxiv.org/pdf/2106.02886), Eqs. 4–5 / Proposition 1 | Uses payoff variance for sparse edges and relates removing an edge to preservation of Max-Sum action choices. | “Decision-preserving graph pruning” is already a direct prior claim. |
| [SOP-CG, ICML 2022](https://proceedings.mlr.press/v162/yang22a.html) | Learns coordination graphs in classes permitting polynomial-time action optimization. | Account for topology and action-solver cost, not only edge count. |
| [Cyclicity-Regularized Coordination Graphs, RLC 2024](https://rlj.cs.umass.edu/2024/papers/Paper40.html), abstract inspected | Topological structure matters beyond independent edge importance. | Include a topology-aware comparator where using coordination graphs. |
| [MUTE, July 2026 preprint](https://arxiv.org/html/2607.03473v1), Eqs. 2–9 and Appendix A/F | Counterfactual message value, joint-return preservation, a conditional performance bound, and Traffic Junction evaluation. It also discusses duplicate-message interactions. | Neither return-preserving message pruning nor adding a traffic demo is a differentiator. It is a necessary close comparator for a communication version. |

Candidate distinction after these collisions:

> The cost of committing to one coordination priority before a resource budget is known, versus choosing a budget-specific information set; the extent to which bounded pre-transmission revision repairs this cost; and how a learned, information-feasible controller exploits that distinction under changing traffic and budgets.

This is a research hypothesis, not an established priority result. The return-transfer lemma below is supporting machinery, not the novelty claim. The literature search does not prove that nobody has studied this combination.

## Decision 4: what is reusable from the ten manuscripts

The seven older filenames refer to their CURRENT contents. Historical filenames such as `master` and `d6` are not stable descriptions of their original agendas. Manuscript abstracts and relevant mathematical sections were read; this was not a new full Lean or experiment gate.

| Source | Useful ingredient for the MARL paper | Boundary that must survive the transfer |
|---|---|---|
| `master.tex` | Calibration-query necessity when nuisance offsets obscure information. | Current calibration model is not an arbitrary learned MARL sensor theorem. Optional unless calibration uncertainty is part of the experiment. |
| `functional.tex` | Actual compression loss and moving-extrema alternatives; scalar proxies can price the wrong problem. | A neighbour-capacity score is not automatically the actual loss of a compressed learned policy. |
| `support.tex` | Decision sufficiency need not require identification; pairwise compatibility does not imply a global common answer. | A joint action must be implementable by the agents; separately acceptable local actions need not form an acceptable joint action. |
| `query.tex` | Information depends on the available query/channel class. | The algebraic exponents need their actual mixture channel, not arbitrary neural messages. |
| `structural.tex` | One ranking/menu across budgets; distinctions between max-of-expectations and expectation-of-max. | A static budget reveal is not temporal graph switching along a trajectory. |
| `adaptive.tex` | Tracking/concentration machinery and limitations of simple quota claims. | Does not already prove convergence or performance of the MARL learner. |
| `d6.tex` | A marginal gap can dominate bounded higher-order interactions in its product-reference setting. | Instantiating the actual response map and its interaction bound is indispensable; a critic score is not such a proof. |
| Current A | The cost of acquiring information using a surrogate design; repair frontier and starvation. | Add only if interaction measurement is explicitly a paid task. A closed-loop policy does not inherit the Gaussian static rate automatically. |
| Current B | Joint-answer obstructions and decision-relevant queries. | Static known-world/channel guarantees must be separated from moving, learned, nonstationary scenes. |
| Current C | Unknown-budget commitment, budget-aware comparison, bounded recourse, generic subset/count-flow tools. | Exact parity constants and one-exchange results are family-specific. Marginal balancing needs an application reason. |

Recommended spine: C + structural, with B/support for information sufficiency and functional/D6 for the loss bridge. A/master/query/adaptive supply only the portions actually needed. Do not require all ten results in the main theorem.

## Decision 5: a concrete decision-level bridge, derived in this session

This is a small analytical construction, not a trained result, not yet a Lean theorem, and not claimed as a novel information-theoretic primitive. Its purpose is to test the proposed storyline on actual team decisions rather than signed sums alone.

### A three-message cooperative decision game

Let X,Y be independent uniform bits and E an independent Bernoulli(p) bit, with 0 < p < 1/2. Three sources possess messages

    M1 = X xor E,    M2 = Y,    M3 = X xor Y.

Two decision agents receive the selected broadcasts and choose actions a1,a2 in {0,1}. Team reward is 1 exactly when a1=a2=X, and 0 otherwise. Both agents can implement the Bayes decision from the common transcript, with a common predetermined tie rule. The sources may have only a communication action; there are two genuine downstream decision agents.

The selector has no free observation of X,Y,E or untransmitted payloads. Its pre-budget order depends only on a public random seed. All messages have equal cost; a subset means paying for and revealing those payloads. This is a one-stage cooperative decision game, which can be embedded in an episodic Markov game; it is not already a moving-traffic model.

Write ell(S) for optimal team failure probability using message set S. Direct conditioning gives

    ell({1}) = p;
    ell({2}) = ell({3}) = 1/2;
    ell({1,2}) = ell({1,3}) = p;
    ell({2,3}) = 0.

Thus the unique best singleton is {1}, while the unique best pair is {2,3}. They are not nested. Per-budget optimum losses are ell*_1=p and ell*_2=0. Extra retained information can be ignored, so this example does not rely on an artificially non-monotone information value.

### Exact randomized commitment price

Choose a distribution P on complete rankings before budget k in {1,2} is revealed. Put

    V = inf_P max_{k=1,2} E_P[ell(prefix_k)-ell*_k].

Let q=P(first item is 1), and r=P(first two items are {2,3}). Necessarily r <= 1-q. Therefore

    regret at k=1 = (1-q)(1/2-p),
    regret at k=2 = p(1-r) >= p q.

Balancing the lower bounds yields q=1-2p and

    V = p(1-2p) > 0.

Attainment: mix ranking (1,2,3) with probability 1-2p and ranking (2,3,1) with probability 2p. Both expected regrets equal p(1-2p). The best deterministic ranking has worst-budget regret min(p,1/2-p).

One pre-transmission replacement after budget reveal removes this commitment regret: at k=1 select {1}; at k=2 select {2,3}. Any fixed-size prefix differs from the desired set by at most one replacement. This achieves the budget-aware LOSS at each budget, not zero loss at k=1.

At p=1/4, all six permutations and the subset risks were checked using exact rational enumeration over the eight (X,Y,E) states: randomized commitment price 1/8, deterministic price 1/4, and one-replacement commitment regret 0. Enumeration checks the algebra; the q,r argument proves the stated symbolic result.

### What this bridge does and does not buy

It connects the C question to actual joint decision error, with noisy individual information and complementary messages. It provides a falsifiable diagnostic for a learned selector. XOR/secret-sharing synergy itself is familiar; this toy result alone is insufficient for a new MARL paper.

It uses a Bayesian risk objective. It is not an instantiation of current B's uniform delta-correct sample-complexity theorem. No marginal fairness band is imposed in this calculation. Adding one changes the feasible ranking laws and requires another analysis. One replacement is pre-transmission recourse: a transmitted message cannot be refunded. Temporal switching and repeated sensing require new accounting.

## Decision 6: the new paper needs three connected results

Working title: **Budget-Adaptive Coordination with Limited Revision**. This is a proposed new MARL manuscript, not a rename of an existing result.

### Result target T1 — commitment and recourse at the decision level

For a public pre-message context z, define an executable decoder d and the team decision loss ell_z(S,d) for an allowed message set S. Let ell*_z(k) be the best loss with k messages under the SAME information and decoder restrictions. Study

    inf_(ranking law P, decoder d) max_k E[ell_z(prefix_k,d)-ell*_z(k)],

and its extension allowing R replacements after k is known but before transmission. Specify whether the max is before or after the random draw. Include all costs of selecting a set, not just its payload.

The three-message construction supplies an exact non-nested example. The next mathematical task is to characterize broader classes: when nested optimizers exist; when commitment has a positive price; and when bounded replacements close or only reduce that price. A statement with explicit approximation/interaction terms is preferable to an unjustified claim that R=1 works for every critic.

The generic C flow bridge is reusable for a subset-dependent cost by using singleton types. This generally costs exponentially many subset states; type compression remains valid only when both objective and feasibility really respect the type symmetry. The flow optimum is a planning/oracle object, not automatically an efficient learned runtime selector.

### Result target T2 — compression certificate to actual control loss

At a joint history h, let K(h) be the SAME feasible joint-action set for all comparators. Define a full approximate critic Qhat and a compressed critic Q_T. An action-independent offset should not count as decision error:

    e_T(h) = inf_c sup_(a in K(h)) |Qhat(h,a)-Q_T(h,a)-c|.

If the implemented joint action a_T is nu(h)-optimal for Q_T, the elementary comparison gives

    max_a Qhat(h,a)-Qhat(h,a_T) <= 2 e_T(h)+nu(h).

This is standard approximation machinery, not a new theorem headline. Local greedy actors do not automatically maximize a joint critic; nu must account for their coordination/inference error, or the architecture must supply an actual implementable joint optimization protocol.

For a reference policy pi_ref, suppose the critic approximates Q^(pi_ref) uniformly over feasible actions at each relevant history to error xi(h). Under the same augmented process (including budget, messages, latency and memory), the performance-difference identity yields the conditional target

    J(pi_ref)-J(pi_T)
      <= 1/(1-gamma) E_(h ~ d^(pi_T))[2 e_T(h)+2 xi(h)+nu(h)].

Here d^(pi_T) is normalized discounted occupancy under the compressed policy. This formulation exposes distribution shift: calibration only under the reference-policy occupancy does not prove the needed bound. A small empirical TD loss does not discharge xi. The full critic need not be optimal, and a learned critic must never be silently called the true Q*.

For a direct decentralized actor rather than a compressed joint critic, use the ACTUAL induced joint action and a teacher advantage estimate. Do not pretend the existing scalar-value `PolicyValueNet` already implements Q_T(h,a) for arbitrary joint actions.

A canonical signed-prefix example transfers only after the residual response is identified with this actual action-dependent function. A nonzero compression norm is not itself evidence that the greedy action or team return changes. T1 addresses that missing implication constructively.

### Result target T3 — uncertainty and genuinely dynamic execution

For the theorem-aligned finite experiment, let A_epsilon(w,h) contain feasible JOINT actions that meet the stated task tolerance in world w. Stop querying only when the remaining worlds admit a common joint action, subject to a valid confidence construction. Every agent must agree on the same joint-action selection rule. The product of individually acceptable action sets is generally unsound.

For moving traffic, messages become stale and queries consume time. At minimum:

- timestamp every observation and message;
- advance the simulator during sensing/communication delays;
- distinguish sensor noise from prediction error and policy learning;
- evaluate on frozen policy checkpoints, then report training variation separately;
- treat any state-drift confidence inflation as a separately assumed/proved model;
- do not reuse the static B likelihood process as a theorem for evolving hidden scenes.

The moving experiment is REQUIRED for this proposed application, as requested. Its safety/return findings remain empirical unless the dynamic assumptions are actually discharged. The controlled finite experiment validates the mechanism; the moving experiment tests whether it survives deployment.

## Decision 7: code that can be reused, and code that cannot be relabeled

Read directly in this session:

- `models/kprefix_net.py`: a Plackett–Luce network emits K complete rankings, with REINFORCE-compatible samples. It structurally enforces nesting within a head. It neither proves optimality nor enforces marginal exposure bands.
- `models/policy_value.py`: actor plus scalar value consumes local observation, explicit-core summary, peripheral summary and belief summary. It is not a joint action-value decomposition. Its batch checks guard against an old duplicated-ego-memory bug.
- `models/core_behavior.py`: full recurrent pair states exist only for active core pairs, but shadow updates read each candidate neighbour's observation/action and relation features.
- `models/peripheral_memory.py`: peripheral inputs include adapter relation features, neighbour last actions and influence/belief data. These require an information-access contract in traffic.
- `scripts/run_paper_b_allocation.py`: historical matched-budget allocation and decision-fidelity diagnostics; its old project label must not be confused with current Paper B.

Important conclusion: the existing core/shadow design can reduce expensive relation-encoder work while retaining broad observation access. It does NOT by itself demonstrate reduced network communication. This is a scope finding, not an accusation that a compute-only experiment is wrong.

Choose and report two budgets separately:

    k_msg: paid neighbour payloads / actual transmitted bytes;
    k_core: expensive explicit relation computations.

A cheap beacon is permissible only with specified content, frequency and charged bytes. For absent messages, the shadow state must use old cached data or a local prediction, not fresh hidden neighbour observations. The selector cannot examine all payloads for free and then claim it only transmitted the chosen subset.

Do not transplant every old causal signal into the new agent. First make a minimal interface:

    public/local history -> rank proposal -> budget reveal -> bounded revision
      -> paid messages -> actor/controller -> world transition.

Use an optional uncertainty head to request additional measurements only when the protocol includes an explicit sensing budget. This prevents A, B and C from becoming three unrelated controllers in one diagram.

## Decision 8: one main traffic experiment, not five simultaneous platforms

Recommended main application for this synthesis: multiple LEARNED vehicles coordinating through a moving intersection in MetaDrive, with occlusions and changing communication/compute budgets. It directly supports the user's B motivation while exposing C's budget commitment and revision question. [Official environment documentation](https://metadrive-simulator.readthedocs.io/en/latest/rl_environments.html) includes multi-agent environments; availability of an environment is not evidence that the proposed protocol is already implemented.

At least two vehicles must learn decision policies. Other scripted traffic can supply disturbances, but one learned ego surrounded by scripted cars is not the intended MARL result. For presentation, show vehicles, occluders, sent messages, unobserved peers, budget, revisions, and resulting joint manoeuvre on the same timeline.

For a traffic-signal version, multiple learned intersections on SUMO are also a coherent choice; [RESCO](https://github.com/Pi-Star-Lab/RESCO) and [LibSignal](https://github.com/DaRL-LibSignal/LibSignal) provide starting infrastructure. That version is closer to the C forecasting/control plan. It is an ALTERNATIVE main application, not an additional mandatory benchmark suite. Do not build both simulators before the mechanism is validated.

The existing C traffic-forecasting proposal can remain a distinct application plan. A forecasting encoder may be an auxiliary component of this MARL system, but forecasting MAE alone cannot validate the new coordination claim. This memo does not cancel or silently rewrite A/B/C.

### Minimal experimental progression

1. **Exact decision game.** Implement the three-message family and exhaustively verify risks, all ranking policies, the randomized optimum and replacement timing. Train a small message selector and decoder to see whether the optimum is learnable. Include p sweeps and held-out p, not just p=1/4.
2. **Small multi-agent traffic diagnostic.** Use a modest fixed map and a learned full-information reference controller. Freeze checkpoints to compare selectors with identical actors/encoders, data and action inference. This isolates selection quality from retraining.
3. **Budget-conditioned learning.** Train a common policy on sampled budgets; add a rank head and a bounded exchange head. Compare against direct subset selection conditioned on the revealed budget and against independent per-budget policies. Count the extra models, selector latency, training and lookup costs.
4. **Moving traffic evaluation.** Evaluate on unseen seeds, traffic densities, occlusion placements and budget traces. Include fixed budgets, unpredictable drops, bursty congestion and shifts not seen during training. Payload collection and revisions consume actual time.
5. **End-to-end adaptation.** Fine-tune the policy and selector together, using the same environment-step and tuning budgets as baselines. Report this separately from checkpoint-preserving compression.
6. **Claims audit.** Trace every plot to source/config/hash, seeds, complete episodes and raw per-run outcomes. Failed/collided/timed-out episodes remain in the denominators. No novelty or simulator success is inferred from a smoke run.

### Baselines must answer the real question

Within an architecture-matched comparison:

- full information / no communication;
- random, attention and historical capacity-score ranking;
- one learned universal ranking, with R=0;
- the same ranking plus R=1,2 exchanges;
- a learned budget-conditioned subset selector without a nesting restriction;
- per-budget retraining or exhaustive subset oracle where small enough;
- unrestricted graph/set revision, with its actual latency and compute cost.

External close comparators:

- CASEC for coordination-graph selection;
- MUTE for return-preserving communication reduction;
- a bandwidth scheduler such as SchedNet or event-triggered method;
- SOP-CG/KINGS if action-inference topology is a major part of the proposed implementation.

Not every baseline fits every backbone. Use a clear two-part comparison: matched-component ablations establish the mechanism; separately reproduced complete algorithms establish competitiveness. Replacing a published algorithm's solver or input access requires labeling the adaptation.

### Figures with a scientific job

F1. The exact three-message decision game: best singleton, best pair, nested commitment gap, one-replacement recovery.

F2. Budget–performance curves: same trained model, all tested budgets, uncertainty across training seeds. Show universal order, bounded revision and budget-aware selection together. This tests the C mechanism rather than just overall reward.

F3. Budget-drop timeline in moving traffic: budget, chosen relations/messages, changes, inference delay, local action loss estimate, actual progress/collision outcome. This makes state drift and revision visible.

F4. Pareto surface or slices: team return/travel time versus actual communication bytes AND inference latency. A single edge-count axis is insufficient if shadow computation or selection is expensive.

F5. Decisions before identification: on the controlled channel, decision error versus world-identification error and paid measurements; on pixels, report empirical uncertainty/calibration separately. This tests B's contribution without claiming algebraic rates for images.

F6. Set interactions: compare predicted single-message effects with actual multi-message removal and budget-dependent optimum sets. Include cases where individual rankings fail and cases where they succeed. Do not assume counterfactual baselines miss all interactions.

Primary traffic metrics: success, collision/near-conflict under an explicit definition, travel time, throughput, timeout rate, and team return. Resource metrics: bytes, messages, query time, selector time, relation-encoder time, peak memory, revisions and stale-message age. Use episode pairs only for matched initial conditions; training seeds are independent units for training variability. Safety shields and fallback WAIT policies must be shared across baselines, and indefinite waiting cannot count as task success.

## Decision 9: what to prove/build first, and when to stop adding ingredients

### Ordered work packages

1. **Freeze the new problem contract.** Specify agents, shared reward, public versus private history, whose budget, reveal timing, message costs, compute budget, revision metric and comparison policy class. Output a small executable protocol plus a statement, not another broad roadmap.
2. **Finish T1 on actual decisions.** Formalize the symbolic three-message calculation; then find a useful broader condition/class for nested sufficiency or a lower bound with bounded recourse. Preserve Bayesian versus uniform-correctness distinctions.
3. **Select the actor/critic interface.** Reuse the existing actor/core/peripheral path if feasible. Decide whether T2 concerns joint Q approximation or the actual induced actor action. Do not assert a theorem for one while implementing the other.
4. **Audit observation and cost access.** Remove free fresh peripheral observations from the communication-limited track. Retain and price them explicitly in a compute-limited track if that is the chosen model.
5. **Build the minimal rank + revision learner.** Start with R=0 and R=1 under hard cardinality; use KPrefixNet as a proposal module, not an optimality certificate. Independent budget-conditioned selection is a mandatory comparator.
6. **Discharge the mathematical bridge that is affordable.** Prove the finite-model decision/return implication with honest error terms. Keep neural critic estimation error visible rather than inventing a uniform guarantee from training loss.
7. **Run controlled and moving experiments in sequence.** Use the exact game to reject broken implementations, then the moving multi-agent traffic system to test benefit. Do not wait for a general Dec-POMDP theorem before the empirical dynamic extension.
8. **Evaluate whether the proposed distinction survives.** If a simple budget-conditioned selector matches the method with cheaper inference and no meaningful revision cost, the recourse algorithm is not yet justified. If universal ranking loses no quality on traffic, report the negative result rather than injecting a synthetic advantage into every traffic scene.
9. **Only then choose publication packaging.** A separate MARL manuscript needs a distinct T1/control bridge/algorithm/evidence package. Existing results must be credited as prior or companion results, not reintroduced as new across several submissions.

### Recommended packaging versus alternatives

| Route | Research question | Fit | Main missing contribution |
|---|---|---|---|
| **New MARL paper, C/structural spine + B/support + functional/D6 bridge** | How does unknown/changing budget constrain decision-sufficient coordination, and what can limited revision recover? | Best synthesis of current assets. | T1 beyond a toy, executable information-feasible learner, controlled-to-moving evaluation. |
| Expand B into cooperative active perception | Which paid inter-agent observations resolve ambiguity that prevents a common team action? | Strong if sensing is the main scientific aim. | Distributed joint-decision protocol and nontrivial dynamic empirical benchmark; arbitrary pixel exponents are not inherited. |
| Expand A into adaptive interaction measurement | Which costly interaction queries should training/acquisition sample to preserve a downstream MARL decision? | Plausible but less direct for an immediate control paper. | Actual response/query model, learning interaction between measurement and policy, a paid-query advantage over direct task-aware baselines. |
| Add MARL as C's application section | Does bounded budget-aware revision improve learned coordination? | Good application extension if modest; risky if presented as a complete new MARL theory. | The same response/control bridge; no automatic transfer of parity or one-swap formulas. |

The new-paper route is recommended to preserve the mathematical scope of A/B/C while restoring the original MARL objective. If the user wants only one final submission, it can instead become a major rewrite with the MARL problem as the organizing question; it should not remain ten theory stories plus a final traffic figure.

## Current confidence and stopping point of this memo

Supported: there is reusable MARL code, a meaningful unknown-budget decision construction, and a coherent synthesis path. The direct collisions with CASEC/MUTE make generic graph/message compression an insufficient novelty claim.

Not established: a new publishable MARL theorem package, competitive training results, one-exchange sufficiency on traffic, universal confidence for a neural policy, or absence of an equivalent prior result. No new training was started, no existing manuscript/ledger was changed, and no Lean gate was run for this proposal. The only new computation was exact rational enumeration of the tiny decision game.
