# MARL scope decision after cheap tests, including the completed Step 3 pilot

This is an independent decision memo. It does not modify the existing scope ledger, producers or historical results. Prepared after reading the user attachment, original MARL_FINAL_SCOPE, heterogeneous exact oracle records, and the NEW completed pilot's collector, trainer, selector, transport, evaluator and raw results. No new training or simulator experiment was launched.

## Decision now

Keep heterogeneous-receiver communication as the one candidate application. Retire the generic latency justification and the presumption that priority plus repair will beat direct selection. The central research uncertainty is now whether useful revisions can be LEARNED and selected economically from legal information.

Step 3's small pilot was justified and has now answered one question negatively: the present 128-wide generic MLP critic plus coordinate repair does not recover most of the oracle advantage on held-out traffic. Do not invest in large actor training or a blind 1,000-context rerun of that same design yet. Allow one bounded learner/calibration diagnostic, with validation deciding expansion, before committing major resources.

## Latest evidence (newer than the pasted status)

`research/marl_budget/hetero_pilot_20260927_181207/test_eval/manifest.json` is COMPLETE. There are 48 snapshots, eight episodes with four independent traffic seed IDs (61–64), four capacity vectors per snapshot and four cost conditions. Raw evaluation has 10,752 rows. Record hash and recorded source hashes match. Independent row checks found no cardinality/self-exclusion/byte-cap violation.

At the predeclared cap of prefix bytes +28:

| Method | Gain over same base prefix | Extra accounted bytes | Positive episode means |
|---|---:|---:|---:|
| true-value R1 search (oracle) | +16.60 | +13.2 | 8/8 |
| public learned R1 | +0.89 | +20.6 | 4/8 |
| public direct local search | +0.94 | +20.9 | 5/8 |
| privileged-summary learned R1 | -0.43 | +20.3 | 4/8 |

Uncapped, exact R1 gains +25.13 and the same coordinate search scored by true values reaches that optimum on this test panel. Public learned R1 gains +1.31 while using +48.6 bytes. These are held-phase H=3 values, not closed-loop traffic delay or throughput. No significance or equivalence claim is established by close means.

This narrows the bottleneck: the tested search CAN reach good solutions when supplied the true evaluator, while the learned evaluator does not reliably choose them. It does not prove data scarcity, information sufficiency or impossibility of learning. Privileged current summaries remain incomplete simulator information.

The earlier exact mechanism panel remains useful: R1 gains +8.45 over an advance order fitted to eight capacity draws; private beats exact known-budget shared orders by +2.76 in mean and in 106/256 cases. These quantities concern a DIFFERENT base order, trajectory distribution and panel from the new +25.13/+16.60; do not pool them or claim the mechanism strengthened merely because the number is larger.

## Required changes to the scope

1. **Deployment premise.** Replace one global grant with heterogeneous receiver decode capacities. Do not claim precomputed priority has a latency advantage in PROTOCOL_v1; per-budget pretabulation defeated that premise.
2. **What is structurally mandatory.** A common stream alone does not force prefixes once receivers may selectively decode explicitly named subsets. Current `profile_cost` lets EVERY method choose the cheaper patch or explicit-set description. Treat prefixes as a low-description baseline, with bounded repair as a constrained algorithm family. Do not remove the direct comparator to manufacture necessity.
3. **Primary learning target.** Focus on whether a local revision improves the current baseline enough to justify its resource cost, instead of assuming accurate reconstruction of all joint-profile values. Test a paired gain target, ranking/decision loss and regularised or structured predictors on the existing training/validation labels before collecting a large new dataset. These are proposed engineering controls, not new theorem claims or guaranteed fixes.
4. **Action policy.** Include “leave the prefix unchanged” explicitly. Measure harmful-edit frequency and its magnitude, not only mean reward. A validation-tuned no-edit threshold is a heuristic unless a valid coverage argument is provided. Do not call neural uncertainty a certificate by default.
5. **Scientific contribution.** Seek a law and algorithm relating revision freedom, interaction-calibration cost and decision quality. The novelty target cannot be merely “shared stream + local search”. A/B should enter through demonstrated acquisition/decision-calibration results; C through the precisely defined joint-profile feasibility/commitment geometry.
6. **Success criterion.** Require improvement on a defensible resource–quality frontier, not universal victory over an unrestricted oracle. With the same cost model and true values, the unrestricted feasible family contains bounded-R profiles, so its optimal value cannot be lower. Possible practical advantages of bounded repair are fewer labels, less metadata, stable adaptation or effective finite-compute search; every such advantage still needs evidence.
7. **The MARL claim.** Keep frozen MP2 for diagnosis. A learned selector on MP2 is not yet learned multi-agent coordination. Train actors and do closed-loop evaluation only after a useful legal-information selector is demonstrated.

## The objective that should be fixed

At permitted context z, prepare an order pi(z). Reveal capacities K and an accounted-byte cap B. Let

    F_{R,B}(pi,K) = {S=(S_i): |S_i|=k_i, i notin S_i,
                    |S_i minus P_i(pi,K)|<=R for each i, cost(pi,K,S)<=B}.

The runtime selector targets conditional team value E[f_X(S) | z,K], not the hidden-state oracle f_x(S). Privileged retrospective regret may be reported but can contain an irreducible information gap. Do not label that whole gap “critic error” without addressing conditioning.

A useful local target is the paired gain

    Delta_x(S;P) = f_x(S)-f_x(P).

Each oracle label pair should share the same restored state and rollout convention. Learning a gain predictor may remove nuisance common offsets, but the existing critic already centres candidate values within context: this change alone is not expected to solve generalisation automatically. The key empirical questions are gain SIGN/ranking quality, harmful edits, budget feasibility and generalisation across independent traffic seeds.

## How the assets fit, with obligations

- **C/T1:** Reachable repairs and structural loss. A single-set/global-radius theorem is not yet a theorem for a product of receiver-specific sets with a coupled team return. A blockwise exchange/realization argument is needed for the stronger structural claim. The generic finite-search error bound can already be formulated on the new feasible family.
- **A:** Proxy-only calibration versus measuring interactions that change the decision. Current uniform/random profile labels do not demonstrate optimized acquisition starvation. Do not claim that bridge from today's negative critic result.
- **B/T2:** Learn one acceptable repair rather than the entire latent world/value table; allocate labels to unresolved repair comparisons. Need actual acceptable-set definition, query law and sample-cost comparison. The needle-class theorem is not a proven calibration law for arbitrary learned traffic critics.
- **Other existing papers:** Reuse valid lemmas, tools and baselines only where instantiated. Do not require all old assets to become separate contributions in this manuscript.

## Minimal next work, not a new large research branch

A. Freeze scope to one heterogeneous protocol and this frozen actor. Correct its textual descriptions and paired resource comparison; preserve all old evidence.
B. Use the EXISTING labels to compare current MSE critic with one simpler/structured alternative and a paired decision/gain objective. Keep data, legal inputs and validation traffic seeds fixed. Report baseline retention, false-positive edits and cost. No extra simulator data is necessary for this first learning diagnostic.
C. If validation yields a useful improvement, acquire a modest next data level using additional independent traffic seeds, with matched rollout-label budgets. Evaluate targeted interaction calibration against uniform/profile sampling only after it is implemented; do not infer its success from A/B analogies.
D. Predeclare a new confirmatory test before comparing the improved method. The 61–64 panel has now informed development. Do not tune thresholds/models on it and continue describing it as untouched.
E. Expand data and actor training only if gains survive resource accounting and beat retaining the baseline. Require competitive value relative to direct selection at some relevant resource level; a practical contribution need not win every metric, but it should not be dominated across all of them.

If these limited changes remain unhelpful, stop the learned-traffic expansion for this submission cycle. Preserve the exact oracle mechanism and mathematical results without claiming an empirically successful MARL algorithm. This is a project resource decision, not proof that the whole research direction is impossible.

## Remaining implementation caveats in the new pilot

- `direct_unrestricted` is a coordinate single-swap search using the SAME critic, not a separately trained budget-conditioned selector or an exact unrestricted optimum. Describe it accordingly.
- The evaluator docstring says the same number of calls. The code uses the same pass limit but does not enforce equal calls: 423/4,608 paired runs differ, by up to 48 calls. Means are close (132.315 versus 132.006), so this does not explain the large oracle/learned gap; correct the claim or enforce a common evaluation cap.
- “Search error zero” here refers to exact R1 versus coordinate search with TRUE scores, uncapped. It does not establish zero search error for an inaccurate learned critic, all byte caps, larger systems, or closed-loop policies.
- Current transport accounts bytes and updates caches but has no wireless airtime, packet loss or execution-delay model. It sends selected payloads before actors act. Do not reintroduce a hard-real-time or physical streaming advantage from these results.
- Raw label/report hashes are present, but evaluation manifests identify a critic directory rather than each checkpoint hash. Record checkpoint hashes for future confirmatory runs; do not use this as a reason to discard otherwise useful pilot data.

## Scope sentence to give the worker

“Study how to learn economically useful bounded revisions of a shared communication schedule under heterogeneous receiver capacities. Separate structural headroom, conditional-information limitations, evaluator error, candidate/search limitations and byte cost. Keep unchanged-prefix and direct budget-aware alternatives available. Claim a learned MARL benefit only after legal-information improvements survive independent-seed, matched-resource and closed-loop evaluation.”

## Follow-up: correct the proposed diagnostics before spending more

### A concrete omission in the legal input

The current public feature vector is time plus the broadcaster's LATEST packet per sender (`envs/external/cityflow_broadcast.py`, `SchedulerContext.features`). But the heterogeneous adapter updates the scheduler for every transmitted packet and updates each receiver only for its own selected subset (`envs/external/cityflow_hetero.py`, `transmit`). Consequently receivers can hold different OLD versions of the same sender's packet. `AgentView.message_from` falls back to that receiver's old cache, and `mp2_action` uses the returned waiting counts. The public MLP input does not represent this receiver-specific delivery history.

This is a verified representation omission, NOT proof that it caused the pilot's poor generalisation. It is particularly relevant because the global-broadcast pilot updated all receivers together, while the new heterogeneous transport does not.

Before buying fresh bids, reconstruct a per-receiver cache from the scheduler's past chosen profiles and the payloads it actually transmitted. In the current loss-free, zero-delay protocol this information is already paid for. Preserve old packet versions, missingness and timestamps. Merely reading the current receiver cache from simulator internals and calling that a legal runtime feature is not an acceptable implementation of this reconstruction. The proof of legal access should be by the public event-history update.

Implementation tasks:

1. `envs/external/cityflow_hetero.py`: maintain a scheduler-owned mirror updated only from transmitted encoded/decoded payloads and the submitted profile, with a read-only context. Do not call fresh `_summary`, `_sensor`, or `views` to build pre-grant context. Return this as an additional feature option; preserve the existing feature contract and outputs for historical reproducibility.
2. Diagnostic assertions: mirror equals actual receiver cache after deliveries; unselected receivers retain the older packet; reset clears it; obtaining features does not invoke a fresh sensor read. Include two histories with the same latest broadcaster cache but different receiver caches. These are meaningful information-access checks.
3. `scripts/MARL_hetero_pilot_collect.py`: record the reconstructed receiver-cache features in a NEW diagnostic artifact. Existing labels do not contain this state; recover by deterministic replay if necessary, verify context/label provenance matches, and reuse the existing labels rather than relabelling every candidate. If replay does not match, report that instead of joining incompatible states.
4. `models/marl_hetero_selector.py` / diagnostic trainer: compare original features with this additional LEGAL history, keeping actor, labels, split and candidate budget fixed. No new bid protocol is needed for this comparison.
5. Use training and validation episodes only for this decision. Seeds 61–64 have now influenced development and must not be described as a fresh confirmatory test again.

### The joint-action diagnostic does not establish the stated causal conclusion

The worker report says value depends on state only through the joint action. Correctly, at a fixed complete snapshot x and held-phase continuation,

    f_x(S) = Q_H(x, a_x(S)).

The reduction is valid ACROSS PROFILES AT THE SAME x. Across snapshots, Q_H still depends on x, including vehicle configuration and routes. Equal joint actions do not imply equal returns.

A critic supplied the true joint action is a useful privileged positive control: success shows a useful feature or bypassed actor-realisation subproblem. It does not prove the current information rule is irreducibly insufficient, nor that a one-byte bid can repair it. Failure likewise does not prove the value unlearnable. Separate prediction of actor action from prediction of its return if this control is used. Fix the legal-history omission above before attributing failure to forbidden fresh information.

### The simple-learner control needs interactions

A ridge regressor on a raw concatenation of context z, capacities K and profile indicator s has form

    f_hat(z,K,s) = a.z + b.K + c.s.

At fixed z,K it ranks all profiles using the SAME c.s in every context. It therefore cannot learn context-dependent communication choices. A negative result from this control would not isolate optimisation trouble. Include regularised context-by-profile interactions, or a simple model that naturally conditions profile gains on context. Standardisation and hyperparameters must use training/validation data only; split by traffic seed/episode, never by individual profile rows.

### What the new Lean theorem and pilot actually establish

`LeanMarlProfileSearchV1` assumes uniform evaluator error on the visited candidate set C, near-maximisation of the evaluator on C (nu), and coverage of the full feasible family F by C in true value (zeta). It explicitly states that none of these empirical constants is established.

- The coordinate routine returns approximately its best scored candidate, so its nu on its OWN visited set can be bounded by the comparison tolerance, assuming deterministic scores.
- A learned scorer and the true scorer can visit different sets C. True-scored search reaching the uncapped exact optimum does not establish zeta=0 for learned search, or at every byte cap.
- Mean MSE, poor test regret and memorisation do not by themselves give the theorem's uniform epsilon. Scores also need conversion from the trainer's normalised units before comparison with raw values (or a correctly shifted/scaled formulation).

Correct the worker's empirical statement to: “Uncapped true-scored coordinate search attained exact R1 on this panel; learned evaluation and/or the candidate coverage induced by it remain limiting.” Logging visited candidates allows subsequent empirical separation of evaluation and coverage errors. Do not claim the pilot has instantiated the Lean bound merely because the theorem compiled.

### Bounded next decision

Run one small training/validation diagnostic comparing the existing critic, a legal receiver-history variant and a properly specified regularised predictor. A privileged action input may be added as a control, not as evidence sufficient to switch protocols. Measure gain over unchanged prefix, harmful-edit rate, accounted bytes, and the same direct-search comparator. Keep prefix as an allowed output. Only a repeatable validation improvement at a relevant resource cap justifies more data and a new confirmatory test. If this diagnostic fails, stop expanding this learned-traffic direction for the present submission; do not automatically add fresh bids, a larger actor or a new simulator.
