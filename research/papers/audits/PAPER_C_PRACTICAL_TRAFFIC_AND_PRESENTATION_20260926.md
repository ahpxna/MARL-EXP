# Paper C: a practical traffic study and presentation plan

Date: 2026-09-26. Research proposal, not an experiment result or a new Lean receipt.

## Recommendation

Study bandwidth-adaptive traffic telemetry: a regional monitor must preserve a fixed aggregate output while only some measurement packets can be transmitted. Compare committing to one priority order, choosing a subset after the packet budget is known, and permitting one swap after budget revelation. The operational question is the value of budget information and a small revision, not whether this paper solves traffic control.

This is a candidate application. Existing C artifacts concern structured weights and perturbations, not deployment on traffic data. A city animation alone cannot close that gap.

## What was consulted

Current A/B model and introduction sections; current C problem, physical interpretation, budget-aware and recourse definitions; abstracts and section structure of the seven originals d6, structural, functional, support, query, master and adaptive. This was a targeted application review, not a fresh line-by-line audit of every original proof or experiment.

Relevant reusable ideas:
- D6: when a ranking has a sufficient margin under the stated product-reference interaction bound. Do not transplant that guarantee to correlated traffic without a new bridge.
- Structural: nonnested budget optima, and the difference between max E and E max. Old menu claims must not override corrected C results.
- Functional: evaluate the actual range objective; frozen extrema can select the wrong design.
- Support: define the acceptable decision first; identifying all hidden causes can be unnecessary.
- Query: what a measurement exposes depends on the admissible observation class. Traffic exponents do not follow from the parity construction.
- MASTER: instrument offset and task dependence. A calibration query is not automatically necessary for every range target.
- Adaptive: implement repeated inclusion/selection probabilities carefully; expected marginal constraints are not pathwise finite-horizon quotas.
- A supplies a support-dependent residual-radius loss beyond a single latent coordinate. B supplies a disciplined way to state the downstream acceptable action. Neither supplies an automatic end-to-end traffic theorem.

## Essential scope correction

In the C model Q_i(z)=g_i z, the even family has sum_i g_i=0, hence F_g(z)=0. An unrestricted estimator can output zero without measuring anything. This does not refute the restricted retained-components-plus-constant compression theorem. It does refute presenting this toy family as evidence that optimal unrestricted traffic sensing needs these measurements.

For the practical study, use varying, nontrivial ground-truth targets and compare against a constant predictor, historical predictor, and a predictor re-fitted to each retained sensor subset. The latter belongs to a larger estimator class and is a separate external comparator, not covered by the C theorem. Do not suppress this comparison if it defeats the proposed use case.

## Operational model

A monitored region has complete boundary inflow/outflow counts. Over a time bin:

    Delta N(t) = sum_boundary_in f_i(t) - sum_boundary_out f_i(t)
                 + internal_starts(t) - internal_ends(t).

Either forbid starts/ends inside the region in a controlled simulation, or account for them. Include all ramps and gates; do not silently omit flow terms. Study the increment, rather than accumulating independent per-bin errors into an occupancy claim without analyzing drift.

Let q_i(t) denote signed contributions, after a training-only baseline if appropriate. A packet conveys one q_i(t). Assume equal packet sizes and costs for the initial study. If k packets are dropped, the estimator retains the other m-k and adds a fixed subset-dependent offset c_S learned from training data. Budget k is revealed once before transmission; an exchange means one selected packet is replaced before either is sent. It is not a free recovery of bandwidth already spent, and not a theorem about arbitrary budget trajectories.

Known at selection: training data, model, timestamp/context permitted to every comparator, current packet budget. Unknown: current values of unqueried sensors and full target. Full information is available only to the offline scorer.

## General support loss: use the actual signals

For a bounded scenario set K, define

    u_S(x) = sum_{i in S} q_i(x),
    L_K(S) = inf_c sup_{x in K} |u_S(x)-c|
           = (sup_K u_S - inf_K u_S)/2.

This is the same half-range structure as Paper A. C's model is the specialization q_i(z)=g_i z. On a finite training support, the optimal offset is the midpoint of the extrema. Freeze that offset for evaluation: optimizing it again on the test support leaks test information and understates deployed error.

Define per-budget regret by subtracting min_{|S|=k} L_K(S), and use exactly the same marginal constraints and decision timing as C. The finite optimization over ranking laws/subset laws/couplings remains well-defined. A count-state reduction requires genuine exchangeable types; arbitrary real trajectories do not inherit C's few-type polynomial size result.

In the first study take 6-10 sensors to permit exact enumeration/LP or certified optimization. Larger instances require a separate scalable algorithm, with primal/dual gap reporting. Do not label a heuristic as the exact C policy.

## An optional bridge theorem worth adding

Suppose on a declared common support K, q_i(x)=g_i z(x)+e_i(x), z(K) subset [0,1] and attains both endpoints, and sup_K |e_i| <= epsilon_i. Let

    E_k = max_{|S|=k} sum_{i in S} epsilon_i,
    E = max_{1<=k<m} E_k.

Then, in unnormalized loss units:

    |L_K(S) - |sum_{i in S}g_i|/2| <= E_k.

Proof: the two residual functions differ uniformly by at most E_k; distance in sup norm to the space of constants is 1-Lipschitz. Their per-budget minimum losses differ by at most E_k, so their regrets differ by at most 2E_k. Since the feasible policy sets are unchanged, each of V, B and V^(R) differs from its ideal-model counterpart by at most 2E. The advantage A=V-B differs by at most 4E. Thus an ideal advantage exceeding 4E guarantees a positive actual advantage on K.

These are elementary derived bounds, NOT checked Lean results. If normalizing, divide by one declared fixed positive common scale. A changing denominator needs a further bound. An empirical residual envelope establishes this only on the observed support, not for all future traffic. This bridge is more relevant to deployment than merely changing constants in the parity gadget, but sensitivity bounds alone are not a novelty claim.

## Why a marginal band may be relevant, and when it is not

A justified use is an explicit equal-service or equal-duty-cycle requirement across identical sensor devices over repeated independent sessions. At a given budget, inclusion probability must be close to the same target for all devices. This is a proposed service policy, not an established physical law of traffic.

Show banded and unconstrained results separately. If a deployment has no such requirement, do not invent fairness to justify the paper. Unequal device costs or heterogeneous minimum coverage require weighted constraints beyond the exact equal-band formulas. Repeated marginal probabilities do not bound gaps between visits or guarantee coverage on every realized run.

## Experiment specification

1. Controlled mechanism: use existing exact four-item/structured-weight results to animate nonnested optima and one exchange. Explicitly label the traffic graphics as an illustration of the restricted compression model. No additional long simulation is needed.
2. Application replay: run or use a SUMO region with complete boundary counts and independently recorded vehicle accumulation. Start with 6-10 gates, fixed traffic controls, and several demand regimes: balanced flow, directional rush, asymmetric disruption. C changes telemetry, not routing or green times. Use scenario/day splits, not random neighboring timestamps.
3. Fit policies, offsets and any latent approximation on training scenarios only. Select tuning choices on validation scenarios. Freeze before held-out evaluation.
4. Compare a common estimator class under: random feasible ranking; scalar-importance priority; optimized single ranking law; budget-aware subset law; and one-exchange coupling with the same initial law and band. An unconstrained priority baseline must be marked infeasible under a tight band, or explicitly converted into a feasible randomized law. Also show unrestricted constant/history/re-fitted-predictor baselines as an external validity check.
5. Evaluate every feasible packet budget; use the same test scenarios and budgets across policies. A sampled ranking is shared across budgets in the single-order experiment. Plot each budget before aggregating. Report max_k E loss and E max_k loss separately if both are shown.
6. Primary practical metrics: error in net vehicle increment per bin, bytes transmitted, number of replacements, optimization latency and actual inclusion frequencies. Report mean absolute error and tail errors; a test maximum is not a population worst-case bound. Secondary downstream metric: missed/false accumulation alerts at a threshold fixed before testing. Do not claim delay reduction without a separate closed-loop experiment.
7. Analyze the operational benefit: reduction in worst-budget expected regret, number of exchanges needed to recover a specified fraction of the budget-aware improvement, and whether that gain survives held-out scenarios, weaker correlation, unequal flow scales and estimator baselines.
8. Statistics: paired comparisons on the same scenarios, uncertainty resampled at scenario/day level to respect temporal dependence. Report solver failures, all chosen regimes, confidence intervals and zero/negative effects. Do not manufacture favorable traffic episodes from test labels.

No full traffic experiment is run by this document. Do not rerun the existing algebraic/LP sweeps merely to create a traffic-looking figure.

## Presentation storyboard

Opening question: "When communication capacity drops, can the same priority list still preserve the traffic signal we care about?"

1. Regional map, entry/exit arrows, and one gauge: net vehicle accumulation. Display available packet slots.
2. Four signed contribution tiles +3,-3,+1,-1. For k=1 the best dropped set is a light singleton; for k=2 it is either opposite pair; for k=3 it leaves a light singleton. No nested path attains all three optima. Label this a model illustration, not measured traffic.
3. Animate a fixed order: dropping +1 then -1 is optimal at k=1,2; adding either heavy item gives absolute residual 3 at k=3, whereas the layer optimum is 1. Show the missing dependency, not just a color-coded score.
4. At k=3 replace one dropped light item with the other heavy item. This changes dropped set {+1,-1,+3} to {+1,+3,-3}, residual 3 to 1. It is one exchange at fixed cardinality. This demonstrates the mechanism, not the general randomized band theorem on its own.
5. Show the C frontier using existing verified figures. Horizontal slider: allowed marginal imbalance. Vertical distance: price of committing before the budget is known. Mark ranges where adaptation offers no gain as prominently as ranges where it helps.
6. Held-out traffic replay: three synchronized panels (fixed order / one exchange / budget-aware), identical traffic trace, packet budget and estimator; traffic movement itself remains identical. Only observed sensors and monitor output change.
7. End with a decision rule: retain a single schedule when the measured/certified commitment penalty is negligible; revise once when it recovers a meaningful gain; pay for full reselection only if extra gain exceeds operational cost. The last tradeoff is measured, not supplied automatically by C.

## Figures with scientific value

F1 mechanism: nonnested dropped subsets at k=1,2,3, with signed sums and one swap.
F2 practical budget curve: held-out monitoring error at each retained-packet count, paired uncertainty; distinguish optimal design bounds from actual test errors.
F3 adaptation recovery: V^(0), V^(1), B versus budget/band, with solver certificates where available.
F4 model mismatch: practical gain against correlation/residual-envelope magnitude; show where the rank-one illustration ceases to predict the outcome.
F5 optional service plot: per-sensor inclusion probabilities and actual finite-run deviations. Expected-band compliance and pathwise coverage are different claims.

## Literature and correct comparison

- Nugroho et al., Where Should Traffic Sensors Be Placed on Highways? https://arxiv.org/html/2110.00912v4 . Equation 8 is the cell conservation law; section IV-A equations 15-18 optimize sensor placement through observability Gramians. This establishes the application neighborhood, not novelty of task-aware sensing.
- Wu et al., Optimal Scheduling of Multiple Sensors over Lossy and Bandwidth Limited Channels. https://arxiv.org/abs/1804.05618 . Sensor scheduling under communication constraints already exists; C should distinguish the all-budget commitment and recourse question.
- Kumarage et al., Demand and state estimation for perimeter control in large-scale urban networks. https://www.sciencedirect.com/science/article/pii/S0968090X23001730 . Accumulation estimation supports traffic management, but C has not proved control improvement.
- SUMO E3 documentation: https://sumo.dlr.de/docs/Simulation/Output/Multi-Entry-Exit_Detectors_(E3).html . Entry/exit detector definitions and within-region outputs can support a controlled setup; use appropriate per-gate counts and complete accounting for starts/ends.
- Caltrans PeMS: https://dot.ca.gov/programs/traffic-operations/mpr/pems-source . Potential subsequent real-data validation. Detector coverage and complete boundary accounting must be checked before using net-flow as ground truth.

## Completion criteria

A convincing presentation is possible now using labeled theory illustrations. A convincing practical claim requires held-out, nontrivial traffic targets, realistic information access, matched constraints, and a visible gain over strong simple estimators. If constant/history/re-fitted baselines erase the benefit, do not call the traffic extension successful. Keep C as a scoped mathematical result and revise the application choice or estimator restrictions openly.
