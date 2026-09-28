# Paper C traffic forecasting: execution specification; Paper B occlusion: proposal audit

2026-09-26. Research/design document, not a report of new training results. No subagents, long experiments, ledger edits or manuscript edits in this pass. The companion `PAPER_C_TRAINED_TRAFFIC_EXPERIMENT_PLAN_20260926.md` remains historical; the corrections below supersede its instructions to re-prove generic flow equivalence and complete its treatment of ex-post evaluation.

## 0. Decision and scope of evidence

C should test **commitment to a nested inference configuration under an unknown compute budget, followed by limited revision**, using actual trained traffic forecasters and held-out forecasting loss. C is not by itself a training algorithm or a traffic controller. The exact signed-family formulas explain mechanisms; they do not become exact neural MAE formulas.

B's occluded-intersection setting is useful, but the pasted proposal is not yet an adequate experiment for the current paper. Its universal WAIT answer trivializes the task. Its generic Gaussian sensor example does not establish higher observation orders. Its proposed exact overlay `log(1/delta)/t*` discards the paper's private/shared-query distinction. Retain the setting and rebuild these parts.

Files whose mathematical/algorithmic bodies were inspected for this application decision include:

- `research/papers/_tex/paper_c.tex`: physical interpretation, timing objectives, budget-aware/recourse definitions, experiments and limitations.
- `research/papers/_tex/paper_b.tex`: obstruction/order, shared tournaments, private queries, critical game, menu design and limitations.
- `work/p13_conjectures/LeanPaperCFlowLawV1.lean`: `rankObj`, `flowObj`, `objective_vectors_agree`, `values_agree`.
- `work/p13_conjectures/LeanPaperCFlowBandJoinV1.lean`: `bandFlowLaw_vector`, `bandFlowLaw_feasible`, `banded_vectors_agree`, signed specialization.
- `work/p13_conjectures/LeanPaperCCountRecourseV1.lean`: transport constraints and cost-facing recourse definitions; the geometric lift should be reused.
- `scripts/EXP_paperC_typed_frontier.py` and `scripts/EXP_paperC_budget_recourse.py`: signed cost, flow/transport constraints, solver returns.
- Previous selected producer/raw-result audit: `BC_PROGRESS_AND_RESULT_AUDIT_20260926_LATE.md`. It records the checked hashes and the limitations of that evidence. This design pass is not a new full gate or a certification of all B/C modules.

## 1. C: what must survive the application bridge

| Existing scientific question | Traffic experiment that preserves it | What cannot be claimed automatically |
|---|---|---|
| One law on complete rankings serves all budgets | Draw one model-component removal order; evaluate its prefixes | Independent masks at every budget are not one ranking |
| Signed cancellation/nonlinear subset loss | Per-example branch outputs and actual multi-branch ablation loss | Mean signed contributions do not represent general MAE |
| Marginal bands have a price | Same objective under explicit balancing bands and without bands | Fairness between neural channels has no automatic operational justification |
| Exact structured frontiers/parity | Retain canonical family theory and its validated plots | Neural losses need not exhibit parity or the exact breakpoints |
| Choice of budget before/after seeing the ranking | Compare max_k E_P r_k with E_P max_k r_k on complete sampled paths | A flow of one-time marginals does not optimize E max |
| Knowing the budget has value | Universal policy versus a per-budget calibrated mask/law bank | The bank cannot be forced to solve online if lookup suffices |
| Limited recourse | R=0,1,2 repairs with a common initial law and final bands | One exchange need not be enough on a neural model |
| Perturbation/stability | Finite calibration and held-out distribution changes, selected-policy error | Stability of optimal values alone does not guarantee a learned policy |
| Exact flow representation | Export a feasible flow and sample an actual law | An LP objective value is not an executable policy |

A useful application preserves these questions, not necessarily all special-case answers.

## 2. C0: fix the deployment contract before training

Write a config/spec containing:

- Forecast target (speed or flow), forecasting horizons, missing-value rules and task loss.
- Budget unit: initially number of active equal-cost computation groups. `k` denotes removed groups, not forecast horizon.
- Runtime information: current past-traffic window and revealed compute budget; no future targets or outputs of skipped groups.
- When an order is drawn and how long it persists. The primary protocol draws it before the budget is revealed. One budget reveal and one repair match current recourse theory.
- Whether all weights are resident or groups must be loaded. Restoring a group requires its weights and state to be available somewhere; count loading/storage.
- Reason, if any, for balanced removal. On one GPU, treat it as a controlled constraint unless an actual duty-cycle requirement exists. Include a no-band track regardless.
- Primary empirical claim: held-out quality versus measured compute/reconfiguration cost, and the value of relaxing the universal-order commitment.

Output: a versioned protocol config. Pass condition: each plotted policy can be executed using only the declared information and resources.

## 3. C1: reproduce a competent forecasting model and clean splits

Use METR-LA first, PEMS-BAY for replication. The DCRNN author repository provides dataset and sensor-location links. A spatial-temporal graph/convolutional backbone is appropriate; STGCN is a reference architecture, not a new contribution here.

Use chronological train / policy-calibration / selection-validation / test portions. Prevent target windows from overlapping across split boundaries. Fit normalization and imputation rules on training data only. Do not use test labels to choose groups, masks, eta, R, architecture or calibration size. Report horizons separately; fix an aggregate horizon objective before optimization if one is used.

Train and check the full network against the chosen implementation under matching preprocessing. Keep full-model errors and failure logs. A poorly trained full model is not a meaningful compression reference.

Output: data/split manifest, full checkpoint(s), prediction arrays, full-model metric report. Start with paired seeds; three independent training seeds are a pilot, not a universal sufficiency rule. Evaluation uncertainty must respect temporal dependence and training-seed variation.

## 4. C2: construct the two model tracks

### Track A: exact additive removal, learned functions

Use independently executable, similarly sized forecasting branches:

    f(x) = f0(x) + sum_i q_i(x)
    f_minus_S(x) = f0(x) + sum_{i not in S} q_i(x).

Each q_i must contain computation that is actually skipped. Splitting only the cheap output matrix while retaining an expensive trunk may have negligible deployment value. Measure the trunk fraction and branch overhead.

Add outputs after branch-local processing. A nonlinear or mask-dependent normalization after summing can destroy the displayed removal identity. Do not deliberately train opposite duplicate branches just to manufacture the signed canonical family.

Start with m=8 groups. Cache branch output tensors on calibration data, retaining sample, sensor, horizon and output coordinates. Do not collapse to one signed mean per branch.

### Track B: standard architecture with structured ablations

Use a standard STGCN-style model with valid dependency-aware channel/block groups. Evaluate actual ablations. Measure the interaction residual

    e_S(x) = f(x) - f_minus_S(x) - sum_{i in S}(f(x)-f_minus_i(x)).

This track asks whether the method is useful beyond deliberately additive models. Exact signed-prefix formulas do not apply to it merely because some ablations correlate.

In the mechanism comparison, freeze the same checkpoint for all selectors. Add shared mask-training/recovery training only as a separately controlled training-regime experiment. Give all selectors the same recovery opportunity and report training costs. Mask-specific normalization has storage/calibration costs.

Outputs: group definition, real skipped-execution forward function, branch tensors where applicable, interaction-error diagnostics and profiled full/partial execution.

## 5. C3: optimize actual subset loss

Define population and calibration costs:

    c(S) = E[loss(Y, f_minus_S(X))]
    c_hat(S) = mean_calibration loss(y, f_minus_S(x))
    beta_k = min_{|S|=k} c(S)
    r_k(S) = c(S) - beta_k.

Use empirical versions for policy selection. Keep any normalization fixed and positive; recomputing a denominator from each noisy subset changes the stability calculation.

For m=8, export all 256 subset costs. m=12 has 4096 subsets. Measure table-generation time. Cache additive outputs offline, but do not compute disabled branches at runtime to select a better subset secretly.

Save task loss and full-model output distortion separately. Actual MAE can improve after an ablation; do not clip that improvement away. Regret is nonnegative only relative to the appropriate per-budget optimum, not necessarily relative to the full model.

Counterexample to the scalar-mean shortcut: a component taking +1 and -1 equally often has mean zero but mean absolute contribution one. The proposed g_i = mean(f-f_minus_i) therefore cannot justify L(S)=|sum g_i|/2 for neural MAE.

Output: a loss table with per-example or temporal-block losses, not just means, plus checkpoint/data/producer hashes. Test labels remain unavailable to policy optimization.

## 6. C4: reuse existing Lean; close the actual missing bridges

### Already present, do not prove again

`banded_vectors_agree` accepts an arbitrary real cost on budget/count states and preserves the band and the whole vector of expected costs. `objective_vectors_agree` is likewise generic. This is stronger than the signed specialization at the end of the file.

For arbitrary neural components, use singleton types (ty = identity). Show reachable count vectors are 0/1 membership vectors, and define the cost by the corresponding subset table. Then instantiate the existing theorem. No symmetry of neural branch contributions is required. The cost is exponential state count, not a false type compression.

### Remaining mathematical work

1. **Subset/count encoding wrapper.** Both encodings preserve set size, item marginals, addition edges and c_hat. Recover universal empirical value from `banded_vectors_agree`.
2. **Generic-cost recourse wrapper.** `CountTransport` already encodes final size, radius and band independently of the signed objective. `transportCost`/`countRecourseValue` currently use `typedCost ty wt`. Parameterize only the cost-facing definitions/results and reuse the existing geometric lift. Instantiate singleton types for neural costs.
3. **Selected-policy transfer.** If sup_S |c_hat(S)-c(S)| <= epsilon, then baselines differ by at most epsilon, regret entries by at most 2 epsilon, and any fixed feasible policy objective by at most 2 epsilon. An empirical zeta-suboptimal policy has true regret objective at most true optimum + 4 epsilon + zeta. With absolute loss and no estimated baselines, the constant is 2 epsilon + zeta. The feasible class must not change with the estimated costs. State explicitly that the bound covers the policy selected using calibration data.
4. **Stochastic assumptions, if asserting a statistical theorem.** For n independent bounded losses in [0,L] and 2^m subsets, a finite-class bound is epsilon = L sqrt((m log 2 + log(2/delta))/(2n)). Overlapping traffic windows are not independent; unbounded MAE does not meet the bounded premise. Supply a legitimate block/mixing model or restrict the real-data claim to held-out empirical evidence. Do not rebrand this standard concentration argument as novelty.
5. **Runtime law correspondence.** Prove/verify that exported transitions and repair kernels induce the optimized occupancies and transports. Source-level cost-table and runtime conventions must match.

The deterministic cost-table transfer also bounds E max objectives by uniform perturbation, but the existing one-time-marginal flow representation does not by itself optimize that objective.

Outputs: small joining modules or proofs with named assumptions, source-to-equation references, then worker compilation and frozen gate. Do not add blanket hcost/hbridge hypotheses and call the bridge discharged.

## 7. C5: implement universal, budget-aware and recourse solvers

For every subset S, let x(S) be its occupancy at layer |S|. Use edges f(S,i) from S to S union {i}. Impose:

    x(empty)=1;
    sum_{i notin S} f(S,i)=x(S)  for nonterminal S;
    sum_{i in T} f(T minus {i},i)=x(T)  for nonempty T;
    x,f >= 0.

At every tested budget k and item i:

    |sum_{|S|=k, i in S} x(S) - k/m| <= eta/m.

For the universal regret value minimize v subject to

    sum_{|S|=k} x(S) r_hat_k(S) <= v  for every k.

Budget-aware: independent probability laws on k-subsets with the same item band. Solve each layer and take the maximum of its optimum; keep all optimizing laws.

Recourse: use ONE initial flow across all k. Introduce z_k(S,T) >= 0, row sums x(S), with |S|=|T|=k and |S minus T|<=R. Enforce the band on the final T-marginal, as well as the initial flow. The final regret inequality uses sum_{S,T} z_k(S,T) r_hat_k(T).

Implement two different repair experiments:

- Joint optimization of initial P_R and all repair kernels: corresponds to V^(R).
- Freeze the R=0 optimum P_0 and optimize its repair kernels: corresponds to repairing a deployed universal policy. It is generally no better than the jointly optimized version. Do not label them as the same curve.

The old signed producers mostly return res.fun. A new empirical solver must return policy arrays, not only objective values. Proposed interface:

    solve_universal(costs, budgets, band) -> x, f, value, diagnostics
    solve_aware(costs, budgets, band) -> per_budget_laws, value, diagnostics
    solve_recourse(costs, budgets, band, R, fixed_initial=None) -> x, f, z, value, diagnostics
    verify_policy(costs, policy) -> independently recomputed residuals/objective

Diagnostics: solver status, constraints checked, primal feasibility, objective, dual bound/gap if available, tolerances, source and dependency hashes. Failed solves remain failed. A feasible minimization objective is an upper bound, not an optimality certificate.

Do not edit legacy producers or running scripts to implement this new experiment. Preserve their historical artifact hashes.

## 8. C6: export and execute the law

At a reached S with x(S)>0, draw next item with probability f(S,i)/x(S). At the revealed budget k, repair to T with probability z_k(S,T)/x(S). Use identical item-label conventions from training through execution.

Handle zero-occupancy rows separately: they are unreachable under an exact law. A numerical fallback is not permission to silently change positive-mass rows. Recompute law feasibility after clipping or normalization. For small m, reconstruct exact numerical path probabilities and verify occupancies; use simulation only as an additional check.

The run must draw a complete ranking (or its equivalent sequential realization) before looking at k. Independent per-k draws from arbitrary subset laws cannot represent universal commitment. Execute only retained groups after choosing T.

Exported repairs may restore components. Record weight storage/loading and the actual number of changed groups. One exchange changes two membership bits, but replaces one selected item; use a consistent convention.

Output: deployable policy artifact, sampling implementation, independent feasibility report and full runtime accounting.

## 9. C7: explicitly preserve the timing story

For the same law P, compute both:

    F_before(P) = max_k E_P r_k(S_k)
    F_after(P)  = E_P max_k r_k(S_k).

The second is always at least the first. It means the budget can depend on the realized complete ranking. It does not automatically mean an adversary observes future traffic noise or future labels; those are different information structures.

Important limitation: occupancy x at each budget does not determine pathwise E max. Flow-to-Markov-law reconstruction preserves each layer, but can change dependence between layers. `values_agree` concerns a functional of the vector of EXPECTED costs, not an arbitrary functional inside the expectation.

Evaluate F_after honestly on the exported law. To optimize it for m=8, a distribution over all 8! = 40320 permutations with each path's max cost is one exact finite LP option. An augmented state carrying the running maximum is another route. Neither is the plain occupancy LP. General recourse with budget chosen after the ranking needs its own joint information-structure definition; do not silently reuse ex-ante per-layer transport values.

No theorem presently turns one budget reveal into guarantees for a repeatedly changing compute-budget stream. Such a stress test may be useful, but label it empirical.

## 10. C8: baselines and matching rules

Mechanism track, same checkpoint and information:

1. Uniform random ranking (zero-band feasible).
2. Magnitude ranking.
3. Taylor/group-saliency ranking.
4. Greedy calibration-loss universal ranking.
5. Optimized universal law R=0.
6. Fixed-initial-law repair R=1,2.
7. Jointly optimized recourse R=1,2.
8. Per-budget calibration-optimal mask/law bank.

Deployment track, account for training differences:

9. A slimmable/multi-width model.
10. Separately trained small models at matched resource levels.
11. Full model as quality/resource reference.

A native deterministic baseline normally violates a tight marginal band. Compare native policies in a no-band track. For a banded track, build and explicitly label a feasible distribution over a baseline's candidate rankings, measure its additional optimization cost, and verify it. Do not claim the projected mixture is the original algorithm.

eta=1 is not generally no-band. For all interior budgets, eta>=m-1 suffices to make every law feasible, or simply implement `band=None`.

The per-budget mask bank is mandatory. Precompute it offline and charge only its real online lookup/reconfiguration cost. If it wins with negligible switching cost, that is evidence that this deployment does not need universal commitment. Do not force it to retrain at every request.

Do not compare a calibrated bank to a test-label oracle without labeling the latter retrospective. Test-set best subsets can be diagnostics, never deployed selection rules.

## 11. C9: the experiment sequence and figures

Run the following after implementation verification. Do not start large training before the small complete pipeline is valid.

| Experiment | Vary | Primary outcome | Figure and interpretation |
|---|---|---|---|
| E0 full-model reproduction | seed/model | forecasting MAE/RMSE, real latency | baseline competence; no pruning claim yet |
| E1 abstraction check | subset, budget, model track | interaction error, actual task loss, selection error | scalar g versus per-example additive residual versus actual ablation; correlation alone insufficient |
| E2 commitment | k, forecast horizon | universal minus calibrated budget-aware loss, worst-budget regret | budget-quality curves for all budgets, not a pooled win |
| E3 repair | R=0,1,2,full | quality, changed groups, actual reconfiguration cost | fixed-P repair and joint optimum as distinct curves |
| E4 marginal bands | eta plus no-band | final/initial marginal deviations and worst-budget quality | empirical frontier; no asserted canonical parity |
| E5 timing | before/after ranking revelation | max E and E max on complete paths | demonstrates the quantifier change, with any optimizing comparator correctly labeled |
| E6 deployment | budget, hardware | p50/p95 batch-1 latency, deadline misses, memory/bytes | quality-resource tradeoff including trunk, selection and loading |
| E7 calibration/OOD | calibration size, held-out day/regime | selected-policy loss and uncertainty | robust transfer; do not transplant a g_m ball bound to an arbitrary network |
| E8 scale | m, candidate policy class | cost-table time, solver time, gap | full lattice only at tractable m; larger approximate search explicitly labeled |

Use paired checkpoints, data windows, budgets and random seeds where appropriate. Distinguish variation over policy randomness, temporal blocks and independently trained models. Keep censored/failed jobs. Do not use every overlapping window as an independent replication.

Report gap-recovery fractions only when the underlying commitment gap is positively resolved; near-zero denominators make misleading percentage gains. Pre-specify practically meaningful quality and latency differences using deployment needs, not the observed best result.

Main figures: (1) budget versus task quality and latency; (2) commitment gap and bounded repair; (3) timing/band tradeoff; (4) actual versus predicted subset damage. Calibration/scalability and per-seed tables may be supplementary. Retain canonical theory figures separately.

## 12. C10: second dataset, ordinary model, and honest stopping criteria

First pilot: METR-LA, m=8, exact table and solver, additive model plus a competent reference, paired seeds. Then ordinary structured-pruning model and PEMS-BAY replication. Expand group count only if it addresses scalability rather than rescuing a preferred conclusion.

Completion criteria for a supported application claim:

- Exported policy is feasible and actually executed without privileged information.
- Trained reference is competent and all baseline budgets/preprocessing are comparable.
- Held-out commitment and/or repair effects are measured with uncertainty. No promise that every regime has a positive gap.
- Any claimed speed/memory/reconfiguration improvement is measured, including overheads.
- Mask-bank and training-based alternatives are included honestly.
- Exact family claims and empirical neural claims stay distinguishable.

Possible negative conclusions are scientifically valid: universal commitment may cost nothing, one edit may not help, balancing may be unnecessary, or a mask bank may dominate. In that case retain C's theory and present a scoped negative/conditional application result; do not create arbitrary deployment restrictions after seeing test outcomes.

## 13. C11: interactive forecasting, not an untested traffic controller

Build a replay from frozen held-out artifacts:

- Map of road sensors; history and ground-truth future traffic.
- Budget slider and active/removed model groups.
- Universal, one/two-exchange and bank predictions on the same scene.
- Forecast error, measured latency and actual changed groups/bytes.
- Optional repeated random ranking draws to display marginal frequencies.
- A separate canonical-theory view for exact parity/frontier/timing; do not relabel synthetic weights as learned traffic contributions.

Cached predictions are allowed when clearly labeled. A visually interactive forecast is already a useful presentation artifact. A SUMO signal-control game requires a further fixed-controller protocol and traffic metrics; improved forecasting MAE alone does not prove lower congestion. CARLA is unnecessary for forecasting completion.

## 14. C12: deliverable layout and dependency order

Proposed new files (names are contracts, not claims that these scripts exist):

    research/paperC_traffic/configs/
    research/paperC_traffic/manifests/
    research/paperC_traffic/data_splits/
    research/paperC_traffic/checkpoints/
    research/paperC_traffic/subset_costs/
    research/paperC_traffic/policies/
    research/paperC_traffic/results/
    research/paperC_traffic/figures/
    scripts/paperC_traffic/prepare_data.py
    scripts/paperC_traffic/train.py
    scripts/paperC_traffic/export_costs.py
    scripts/paperC_traffic/solve_policies.py
    scripts/paperC_traffic/verify_policy.py
    scripts/paperC_traffic/evaluate.py
    scripts/paperC_traffic/profile.py
    scripts/paperC_traffic/replay.py

Priority chain:

    protocol -> full-model reproduction -> actual subset table
      -> generic-cost proof instantiation + policy-returning solver
      -> independent feasibility checks -> exact small pilot
      -> ordinary model + replication -> hardware metrics -> figures/replay.

Math and solver work can proceed while a frozen training job runs, but never change its producer/config while it is generating a source-hashed artifact. Print real long-run commands only after scripts/configs exist and dependencies are checked; do not invent executable commands in this plan.

## 15. B: audit of the pasted MetaDrive proposal

### B1. Universal WAIT makes the stated task vacuous

If WAIT belongs to every A(w), their global intersection is nonempty. Order zero and zero queries solve the problem. Paper B says this explicitly. Giving reward +1 for a safe action then trains an always-WAIT policy. The Minecraft RETREAT example has the same flaw.

Repair the TASK, not the safety label. Define physical safety and acceptable service/progress separately. For example,

    A_epsilon(w) = {a : risk_w(a)<=alpha_phys,
                         delayCost_w(a)<=Cstar_w+epsilon},

where Cstar is the minimum delay cost among physically safe actions. A waiting macro-action may be safe but unacceptable when it causes unnecessary delay, while remaining acceptable in dangerous worlds. Do not falsely call waiting a collision. Emergency abstention remains available operationally, but count it as abstention/timeout, not a completed successful decision.

Derive A(w) from specified finite-duration maneuvers and scenario rollouts; do not write a convenient answer table disconnected from dynamics. Require every world to have a valid action and at least one obstruction to exist. If risk/utility are estimated, record their uncertainty; a simulation estimate is not exact safety certification. delta is the statistical probability of selecting an invalid answer, not the physical collision tolerance alpha_phys.

A controlled three-world check is A(w1)={a2,a3}, A(w2)={a1,a3}, A(w3)={a1,a2}. Every pair has a common answer but the triple does not. Three crossing-time windows with one blocked window per scenario can illustrate this, provided the simulator really realizes the declared losses. Larger co-safe constructions require matching action/world counts; a 20-world/3-action scene does not automatically instantiate the paper's m-world parity tip family.

### B2. Decision before identification is only one layer of the paper

Overlapping decision regions and their hyperedge obstructions already appear in Javdani et al. The current B story additionally includes graded information orders, continuous-noise cancellation, per-world versus minimax order, shared/private query allocation, critical coefficients and sensor-menu design.

The proposal's visually compelling early stop demonstrates the first layer. It does not by itself test the statistical exponent or the critical game. Generic active sensing or a better PPO reward is not a substitute.

### B3. Generic Gaussian sensor noise does not give the order hierarchy

A channel Y=mu_wq+Normal(0,sigma_q^2) with all mean gaps proportional to h typically has visible information order one. Increasing noise uniformly may worsen constants without creating the paper's arbitrarily separated powers.

Use the existing parity/latent continuous channel for the controlled order experiment, with its actual h-dependence and proved noise laws. Render it as a sensor abstraction if useful, labeling that abstraction. Native camera/radar inputs can be a separate empirical extension. A hand-assigned separation order or a log-log slope from generic noisy images does not instantiate the theorem.

### B4. t* is not an exact oracle sample count

The current paper proves a coarse obstruction lower bound and an upper schedule with cardinality factors. Its shared schedule uses at most

    min(|Q|, |W|^2) ceil(log(|W|/delta)/t_H*).

The private-query example shows why t* cannot determine the exact constant. The rescaled information game has a critical coefficient game G*, under its expansion hypotheses. Therefore distinguish:

- s*: signal-strength exponent;
- G*: critical information-game constant;
- actual stopping cost of a specified algorithm at finite h,delta.

Do not draw log(1/delta)/t* as an exact achieved prediction. An optimized-game limit alone also does not prove that a chosen neural policy attains that limit.

Add an experiment with shared and private queries at the same orders, and show different allocation burdens. This is missing from the pasted proposal and is central to B's current story.

### B5. Freeze the scene, but check the channel law too

Freezing the world avoids dynamics during sensing, which is appropriate for the initial protocol. It does not make repeated sensor readings conditionally independent. A cached deterministic image is the same information on every query; fresh augmentations are not necessarily physically new evidence. If fresh independent sensor noise is simulated, state its law. Persistent nuisance variables belong in the hidden world or in a justified conditional-history model.

Do not move the ego vehicle during inspection while still claiming a fixed memoryless query channel. CREEP may be a terminal macro-action; a sensing maneuver with state evolution is a separate dynamic extension. Query-cost savings in a frozen scene are not proven real-time driving safety gains.

MetaDrive's default observation can contain ego/navigation state and surrounding vehicle state. Use a whitelist custom observation and test occlusion/hidden-label leakage. An unoccluded top-down map is privileged visualization, not an allowed observation. RGB/depth/semantic/LiDAR support is documented; native MetaDrive radar was not established by the documentation checked. CARLA has a separate sensor stack; porting is engineering work, not an automatic consequence of a shared narrative.

### B6. Train perception without pretending reward gives delta-correctness

A finite collision penalty or posterior threshold does not establish uniform frequentist correctness. Under a known finite channel, use the existing valid testing machinery, or an explicitly proved confidence-set construction. One sufficient standard construction with positive likelihoods is:

    L_t(w)=product_{s<=t} p_w^{q_s}(Y_s).
    Eliminate w if some v!=w at some s<=t has L_s(v)/L_s(w)>=(|W|-1)/delta.

For predictable queries and the correct model, under true w each likelihood ratio is a nonnegative martingale. Ville plus a union bound over v gives truth survival for all t with probability >=1-delta. This is standard machinery, not a new result.

Decision stopping: H_t must be NONEMPTY and intersect_{w in H_t} A(w) nonempty. Identification stopping: H_t is a singleton. Empty H_t is a model/numerical failure or an abstention; never exploit the empty intersection convention to return an arbitrary action.

Start by running the same acquisition schedule with the two different stopping criteria; then compare specialized acquisition policies. This isolates stopping savings from query-selection savings.

For learned images, use a trained encoder/likelihood model with calibration and held-out scene tests. A neural posterior is not the exact channel law. Report empirical error with uncertainty and abstentions, rather than borrowing the known-channel theorem. Split simulator layouts/occluders/traffic actors between train, calibration and evaluation where testing generalization. Repeated renders of one seed are not independent unseen worlds.

### B7. Improve baselines and cost accounting

Identification-first is necessary but insufficient. Include uniform sensing, information-gain acquisition, a decision-region acquisition comparator, the paper's shared-observation schedule, and an information-game allocation diagnostic where computable. Use established multiple-answer sequential algorithms only where their assumptions actually instantiate. The original HEC/DRD paper assumes noise-free observations; a noisy adaptation must be specified, not described as running its original theorem unchanged.

Match sensors, hidden-world prior or worst-world evaluation, fresh-noise laws, unit costs, action set and risk target. A prior-weighted average success rate can conceal an unsafe rare world. Report per-world/worst-world invalid-answer rates and costs, as well as averages.

Separate one-time sensor INSTALLATION cost from per-query USE cost and actual sensing latency. The unit-query theorem does not automatically give cost-weighted optimality for arbitrary cameras/radar prices.

### B8. Keep world identification meaningful

Do not inflate the ID baseline with texture IDs, scenery colors or arbitrary nuisance labels that the task deliberately ignores. Define behavioral world labels before measurements and report the granularity. If no allowed query distinguishes some worlds, exact ID may be impossible; report that, not a very large finite cost. If an unresolved class is also an obstruction, decision is impossible too.

Menu design hits every obstruction with at least one distinguishable pair at the target order. It does NOT require separating every pair of every world (that would revert toward identification).

## 16. B: revised work order preserving the full story

1. **Reuse the existing continuous parity/latent experiment** for law/order validation; no need to add RockSample as a compulsory new prerequisite.
2. **Define a non-vacuous finite traffic decision task:** fixed macro-actions, physically safe plus service-qualified acceptance sets, obstruction enumeration, full-state oracle used only for generation/evaluation.
3. **Known-channel traffic layer:** finite W,Q, query law and noise explicitly specified, valid stopping, matched-ID comparator. Label a synthetic sensor abstraction honestly.
4. **Order experiment:** sweep h with fixed W,Q; compare safe and ID exponents under the proved controlled channel. Preserve censoring and distinguish upper budgets from two-sided sample-complexity estimates.
5. **Constant experiment:** shared/private query channels with the same orders; compare the computed critical game and actual cost without asserting finite-delta exact equality.
6. **Menu experiment:** enumerate or solve the sensor-installation hitting problem at a target order; test losing one essential query, adding a redundant query, and adding an order-changing query.
7. **Train a visual encoder in MetaDrive:** initially keep decision logic/testing interpretable and separate from perception training; use supervised query observations and held-out layouts. End-to-end RL is an optional ablation, not the first proof bridge.
8. **Evaluate:** invalid-answer risk, physical collisions and task progress separately; paid queries, sensing costs, abstentions, caps, completion delay and residual world uncertainty. Show performance versus achieved risk, not only configured delta.
9. **Replay:** common scene side-by-side, paid sensor sequence, surviving worlds, acceptable-action intersection, stopping reason, final rollout and costs. Do not show privileged state to the acting policy.
10. **Only later:** moving-scene sensing, CARLA rendering or Minecraft. These are separate extensions, not requirements for completing the principal benchmark.

B completion means the task is nontrivial, the actual query/answer structure is documented, the order and allocation layers are tested in their valid regimes, and the visual application reports its learned-channel limitations. A nice early-stop video alone is not completion.

## 17. Minimal story coverage matrix for the final papers/presentation

| Story component | C evidence | B evidence |
|---|---|---|
| Global task | Forecast under unknown inference budget | Reach a valid timely driving decision under hidden scene |
| Local decision | Which group to remove/restore | Which observation to buy and when to stop |
| Coupling across choices | Same ranking across all budgets | Same query can inform several world pairs |
| Fundamental cost | Commitment/band/timing price | Obstruction information and observation order |
| Repair/design | Few exchanges, calibrated policies | Sensor-menu design, critical allocation |
| Learned application | Actual neural forecast loss and real latency | Learned sensor processing and held-out driving scenes |
| Exact theorem evidence | Canonical family plus generic cost-flow instantiation | Controlled continuous channel plus valid finite-world tests |
| Scope boundary | No universal parity/one-swap neural theorem | No automatic pixel exponent or dynamic-driving safety theorem |

## 18. Primary sources and what each supports

- STGCN architecture/implementation: https://github.com/VeritasYin/STGCN_IJCAI-18 . Convolutional traffic forecasting is established; use it as infrastructure/comparator.
- DCRNN data and location links: https://github.com/liyaguang/DCRNN . METR-LA/PEMS-BAY inputs and maps.
- Once-for-All: https://hanlab.mit.edu/projects/ofa . Train-once/deploy-many is established.
- Universally Slimmable Networks: https://openaccess.thecvf.com/content_ICCV_2019/html/Yu_Universally_Slimmable_Networks_and_Improved_Training_Techniques_ICCV_2019_paper.html . Existing runtime-width approach; include a training-based baseline.
- Taylor importance: https://openaccess.thecvf.com/content_CVPR_2019/papers/Molchanov_Importance_Estimation_for_Neural_Network_Pruning_CVPR_2019_paper.pdf . Stronger pruning comparator than magnitude.
- DepGraph: https://openaccess.thecvf.com/content/CVPR2023/papers/Fang_DepGraph_Towards_Any_Structural_Pruning_CVPR_2023_paper.pdf . Valid structural dependencies matter.
- MetaDrive observation documentation: https://metadrive-simulator.readthedocs.io/en/latest/obs.html . Sensor options/custom observations and privileged-state leakage risks.
- MetaDrive sensors: https://metadrive-simulator.readthedocs.io/en/latest/sensors.html . Supported sensors; do not assume undocumented modalities.
- CARLA sensors: https://carla.readthedocs.io/en/latest/ref_sensors/ . Separate engineering platform; not needed for first completion.
- Zhang and Fisac, RSS 2021: https://roboticsproceedings.org/rss17/p066.html . Safe occlusion-aware active perception already has driving literature; the application context alone is not novel.
- Javdani et al., AISTATS 2014: https://proceedings.mlr.press/v33/javdani14.html and https://proceedings.mlr.press/v33/javdani14.pdf . Overlapping decision-region/hyperedge geometry is prior art. Original paper's limitation: noise-free observations.
- Degenne and Koolen, NeurIPS 2019: https://proceedings.neurips.cc/paper/2019/hash/60cb558c40e4f18479664069d9642d5a-Abstract.html . Multiple-correct-answer pure exploration is prior machinery.
- Guney et al., ICML 2025: https://proceedings.mlr.press/v267/guney25a.html . Learned active feature acquisition is established; a neural query policy alone is not the distinguishing contribution.

These are targeted primary-source checks, not an exhaustive literature or publication guarantee. This document specifies proposed work; it reports no new trained-model performance.

## 19. User steering: restore the MARL application, and include moving traffic in B

This section supersedes the earlier decision to leave dynamic traffic outside the principal application package. The user explicitly wants moving traffic alongside the theorem-aligned experiment and asks why the original MARL motivation disappeared.

### 19.1 What the historical files actually say

`research/new_chains_v2/ACTUAL_EXPERIMENT_RUN_CHECK.md` records H1 and OmniArena development episode runs, but explicitly labels them plumbing/development rather than confirmatory results. `EXPERIMENT_READINESS_MATRIX.md` records partial learned-MARL adapters and a missing production F3 adapter. These are historical snapshots, not a claim that the current runner is usable without inspection. Its old “Paper-B” runner label must not be confused automatically with today's obstruction-order Paper B.

`research/imported_codex_tree_20260907/KE_HOACH_6_PAPER_20260907.md`, Structural completion criterion, explicitly says not to make the theory paper wait for KPrefixNet/deep MARL. The current A/B/C statements then isolate statistical decision and combinatorial design problems. This explains a documented direction of travel: MARL motivation -> abstract subproblems -> independently publishable theory. It does not establish a MARL experiment or a MARL return guarantee.

The previous recommendation continued that separation too far by making C supervised forecasting alone and B one-vehicle static sensing. That is useful mechanism work but does not satisfy a MARL application goal. The remedy is a trained multi-agent closed-loop evaluation with the paper's decision variable isolated, not adding “MARL” to captions.

### 19.2 Revised application targets

- **C:** resource-limited forecasting inside cooperative multi-intersection traffic control. First establish the forecasting/compression mechanism, then test the same configurations as inputs to multiple learned signal-control agents. Include this closed-loop MARL evaluation in the application package.
- **B:** cooperative active sensing in a moving multi-vehicle intersection. Keep the controlled finite-world channel test for exact mechanism checks, and include a real-time moving-scene evaluation as a principal empirical extension. Both remain part of the deliverable, with different guarantee labels.
- **A, only as a research-map connection:** decision-directed measurement allocation could serve relation/traffic estimation in MARL, but that bridge is not implemented or proved merely because B/C have a simulator. Do not broaden the present work package to implement A simultaneously.

Multiple sensors, road nodes or scripted cars are not enough to call an experiment MARL. Identify learned agents, their local observations/actions, interactions, training objective and execution information. A centralized resource allocator attached to trained decentralized agents is permissible, but describe that architecture explicitly.
