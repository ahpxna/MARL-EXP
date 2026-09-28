# Paper C: trained traffic models, empirical commitment cost, and limited repair

Research/design memo, 2026-09-26. Proposed experiments; **no new training or empirical performance is reported here**. This complements PAPER_C_PRACTICAL_TRAFFIC_AND_PRESENTATION_20260926.md. No progress ledger or manuscript has been edited.

## 1. Decision and scientific question

Build a substantial experiment on **traffic forecasting with a trained convolutional model**, followed by an interactive replay and, if justified by the offline results, a traffic-control demonstration. The contribution to test is:

> With a fixed trained model and inference budget not known when an order is committed, how much quality is lost by requiring one nested removal order, and how much of that loss can a bounded number of component exchanges recover?

Train-once/deploy-many, channel importance, and traffic-network pruning already exist. Do not claim a new training algorithm or a new general traffic controller just because Paper C selects the active components.

Use two evaluation tracks:

1. **Mechanism track:** same trained checkpoint, same groups, same calibration data, same permitted information, same budget, same balancing constraints. Only the removal/repair policy changes.
2. **Deployment track:** separately trained small networks and a slimmable model, with their training/search/fine-tuning costs reported. This checks whether the mechanism has a competitive practical consequence.

An actual experiment may show that a mask bank or a small trained model is better. Retain this result. The objective is a defensible application, not a preselected victory.

## 2. Closest literature checked and consequences

Primary sources consulted in this research pass:

- Once-for-All (ICLR 2020), author project and abstract: https://hanlab.mit.edu/projects/ofa . Training one network for diverse deployment configurations is established.
- Universally Slimmable Networks (ICCV 2019), official paper: https://openaccess.thecvf.com/content_ICCV_2019/html/Yu_Universally_Slimmable_Networks_and_Improved_Training_Techniques_ICCV_2019_paper.html . Arbitrary runtime widths, sandwich training and in-place distillation are established machinery.
- FlexMoE (2026), primary full-text Method/Experiments/Deployment sections: https://arxiv.org/html/2606.27866v1 . Nested pruning across budgets, shared recovery fine-tuning, and online budget switching with implementation work are close prior art. Its LLM experiments are not a directly executable traffic-CNN baseline. Cite the distinction; do not reproduce the scale of its LLM training.
- SPvR (UAI 2025), official proceedings abstract: https://proceedings.mlr.press/v286/hassan25b.html . Ranking-based structural pruning exists; this work trains the pruned networks from scratch, so a comparison against an unfine-tuned checkpoint must label the training difference.
- Molchanov et al., Importance Estimation for Neural Network Pruning (CVPR 2019), primary paper: https://openaccess.thecvf.com/content_CVPR_2019/papers/Molchanov_Importance_Estimation_for_Neural_Network_Pruning_CVPR_2019_paper.pdf . Taylor importance is a necessary stronger comparator than magnitude alone.
- DepGraph (CVPR 2023), primary paper: https://openaccess.thecvf.com/content/CVPR2023/papers/Fang_DepGraph_Towards_Any_Structural_Pruning_CVPR_2023_paper.pdf . Structural dependencies and actual removal of computation matter; zero masks alone do not establish acceleration.
- Joint Dynamic Pruning Method for GNN traffic prediction (Transportation Research Part C, 2026): https://researchportal.hkust.edu.hk/en/publications/joint-dynamic-pruning-method-for-graph-neural-networks-under-traf/ . The institutional abstract reports graph and parameter pruning. Publisher full text was not accessible in this pass; no theorem-level collision conclusion or implementation equivalence is asserted from its abstract.
- STGCN, author implementation and evaluation protocol: https://github.com/VeritasYin/STGCN_IJCAI-18 . A convolutional traffic forecasting backbone and real sensor datasets.
- DCRNN, author implementation/data links: https://github.com/liyaguang/DCRNN . METR-LA and PEMS-BAY data and locations are available through its documented links.
- BasicTS, author benchmark repository: https://github.com/GestaltCogTeam/BasicTS . Useful for consistent data processing, metrics and comparison infrastructure; pin a version and verify its chosen model implementation.
- RESCO: https://github.com/Pi-Star-Lab/RESCO ; LibSignal: https://github.com/DaRL-LibSignal/LibSignal . Existing traffic-control benchmark infrastructure, preferable to inventing a simulator.
- Sim2Signal (2026), primary abstract and full-text structure: https://arxiv.org/html/2609.01676v2 . Simulator/controller performance has observation, action, transition and reward gaps; a game video is not deployment validation.

This is targeted literature research, not a systematic or exhaustive priority certificate. The empirical novelty candidate is **measured commitment cost and quality-versus-exchange-cost recovery**, with the exact Paper C family explaining a mechanism. Generic elastic inference is not the new claim.

## 3. Fix the proposed mathematical bridge before training

### 3.1 Do not replace the contribution function by its signed average

Let Δ_i(x)=f(x)-f_{-i}(x). Setting g_i=E Δ_i(X) can erase damage: Δ_i(X) can take values +1 and -1 equally often, giving g_i=0 but E|Δ_i(X)|=1. Correlation between a scalar surrogate and accuracy is also insufficient to establish good subset selection at each budget.

Save a contribution tensor over calibration examples and outputs, not just one number per component. Check both average and tail errors and whether the selected subsets remain good on held-out days.

### 3.2 Distinguish exact additive removal from interacting ablations

For a deliberately grouped additive forecasting head,

    f(x)=f_base(x)+Σ_i q_i(x),
    f_{-S}(x)=f_base(x)+Σ_{i∉S} q_i(x),

so f-f_{-S}=Σ_{i∈S}q_i exactly, with vector-valued q_i permitted. Each q_i must include a physically skippable computation group; merely splitting a final linear matrix does not remove the expensive shared trunk.

For an ordinary network, explicitly measure

    e_S(x)=f(x)-f_{-S}(x)-Σ_{i∈S}Δ_i(x).

Single-ablation agreement does not bound e_S at larger budgets. Never assign the exact additive theorem to an arbitrary deep pruned network.

### 3.3 Do not equate the original half-range loss with MAE or accuracy

The manuscript's |Σg_i|/2 is a best-constant worst-case residual on shared binary support. A neural forecasting MAE, squared error, or classification accuracy is a different loss. A calibration-fitted bias correction is permitted if every comparator receives the same option and the correction never uses test targets.

Use actual validation task loss as a cost table for the empirical optimization; use output-residual distortion as a separate diagnostic. Exact parity formulas remain restricted to the stated family.

### 3.4 Equal exposure requires a real deployment reason

There is no inherent fairness claim between CNN channels. For distributed modules on different edge devices, an operational duty-cycle constraint may justify balancing. For channels on one GPU, describe balancing as a controlled experimental constraint unless a real requirement has been established.

Always include **unconstrained** results. η=1 is NOT generally an unconstrained band: the condition is |p_i(k)-k/m|≤η/m. Taking η≥m-1 makes every law feasible over all interior budgets; otherwise use an explicit no-band variant.

### 3.5 Do not manufacture a benefit over a mask bank

If all weights are resident and all per-budget masks are precomputed, mask lookup can be essentially free. An arbitrary mask bank may dominate a universal order. Include it.

A systems advantage of few exchanges needs a measured cost: loading bytes, changing a deployed configuration, kernel/layout rebuilding, cache disruption, or an actual bound on which components can be replaced. Count only work actually incurred by each method. Never force the mask-bank comparator to retrain or solve online when it can precompute offline.

## 4. Concrete task, models, and training

Primary data: METR-LA; independent replication: PEMS-BAY. Use official time ordering, missing-value handling and train/test split. Divide the non-test portion further into training, policy calibration and hyperparameter validation without overlapping target windows across boundaries. Fit normalization using training data only. Report forecasting horizons such as 15/30/60 minutes where supported by the chosen preprocessing.

Model A: a compact spatial-temporal convolutional predictor with a shared trunk and 8 independently executable, equal-cost residual branches. Add their output forecasts linearly. This is an explicitly modified architecture for an exact additive mechanism test; do not label it the unmodified STGCN benchmark architecture.

Model B: a standard STGCN-style network with valid structured channel groups and measured, potentially non-additive ablations. This is the generalization test beyond the additive construction. Start with 8 groups in a specified prunable region; consider 12 only after the end-to-end pilot is informative.

Training protocol:

1. Train the full models on the same supervised traffic objective. Check that full-model accuracy is reasonably competitive with the reference implementation under the same preprocessing; a bad teacher can make compression look artificially easy.
2. Initially freeze all weights and normalization statistics during the mechanism comparison. Group definitions, ordering scores and correction coefficients use calibration data only.
3. A separate training-regime ablation may use random-mask training, sandwich training/distillation, or common recovery fine-tuning. All compared selectors must receive the same training resource in that ablation. Use fixed normalization or explicitly account for mask-specific normalization storage/calibration.
4. Use at least three independent training seeds for the pilot estimate; expand only if uncertainty changes the conclusion. Match seeds and checkpoints across selectors. Do not count thousands of correlated test windows as thousands of independent trained models.
5. Record actual MACs, batch-1 median/p95 latency, peak memory, parameter storage, and setup/search time. Include the shared trunk and mask selection. Parameters still held in memory do not disappear because their branch is skipped.
6. Keep a separately trained small model and a slimmable model as deployment comparators, with their training costs and method adaptations explicit.

Do not train a giant transformer or an RL controller merely to make this extension look modern. The experiment must isolate the paper's decision variable: a ranking and a bounded revision.

## 5. Implement the empirical algorithm, not just a traffic skin

Let c(S) be expected task loss after removing S; estimate it by a calibration cost table ĉ(S). For m=8, there are 256 subsets; for m=12, 4096. Actual network evaluation to construct this table may dominate the optimization, so measure it. Additive branches allow their outputs to be cached offline; no such cache may leak unavailable test outputs at runtime.

Define β_k=min_{|S|=k} c(S) and r_k(S)=c(S)-β_k, optionally divided by a fixed positive calibration scale. This is an **empirical task-loss extension**, not an identity with the original signed objective.

Universal objective:

    min_P max_k E_P r_k(S_k(π)),
    |P(i∈S_k)-k/m|≤η/m.

Use the full subset lattice: nodes S, edge S→S∪{i}. A unit flow induces one law on complete rankings. Use a separate epigraph inequality at every budget. No averaging away the difficult budgets.

Budget-aware comparator: solve an independent subset-law LP at each k under the same band. Recourse: retain one common initial ranking law, with per-budget transport S→T satisfying |S|=|T|=k and |S\T|≤R. Impose the band on both initial and final laws.

The direct finite subset formulation works for any measured cost table. The paper's compact type reduction requires identical cost behavior under within-type permutations; grouping neural modules just because their mean contributions are close does not justify it. Full subset states are exponential in m. Label any larger-model beam search or sampled candidate menu as an approximation; it is not an optimum over all rankings. Save primal feasibility, dual bounds where available, solver status and gap.

Runtime: commit/draw the ranking; observe the available budget; apply its prefix and the precomputed permitted repair mapping; run only retained groups. Current test labels and outputs of disabled groups cannot select the mask. If a cheap input-aware selector is introduced, count its compute and label that as an additional method outside the budget-only theorem.

## 6. Minimal mathematical completion for this bridge

Two short results are useful; neither is claimed as new sensitivity or statistical-learning machinery.

**A. Cost-table flow identity.** State and prove the finite-subset flow/ranking correspondence for an arbitrary fixed cost c(S), preserving every item marginal and expected budget cost. This extends the computational mechanism to measured neural losses. Recover the existing signed objective as a specialization. For the empirical scale m≤12, singleton types/full subsets avoid an unjustified symmetry assumption.

**B. Uniform-estimation transfer for the selected policy.** Suppose sup_S |ĉ(S)-c(S)|≤ε. Then |β̂_k-β_k|≤ε and every regret entry differs by at most 2ε. Consequently any fixed feasible universal/recourse policy has objective error at most 2ε, and the corresponding optimum has error at most 2ε. If P̂ is ζ-suboptimal for the empirical regret objective, then

    true_objective(P̂) - true_optimum ≤ 4ε+ζ.

Proof: insert empirical objective(P̂), empirical optimum, and true optimum, paying 2ε, ζ and 2ε. Feasible sets must be the same and independent of estimated costs. For absolute task-loss objectives without estimated per-budget baselines, the bound is 2ε+ζ.

This selected-policy guarantee does not follow merely by quoting stability of optimal values in ||ĝ-g||₁.

For independent bounded calibration samples with loss in [0,L] and at most 2^m subsets, a Hoeffding union bound yields

    ε_n = L sqrt((m log 2 + log(2/δ))/(2n)).

This is a finite-class cost-table result, not a rate for ||ĝ-g||₁. Overlapping traffic windows are not independent samples. Either justify a mixing/block argument, use independent episodes under its assumptions, or limit the real-data statement to an empirical held-out evaluation. Do not clip losses without disclosing that the guarantee then concerns the clipped objective.

The pasted proposal's blanket O(sqrt(m/n)) claim for an L1 weight estimate is not valid: if n observations estimate each of m coordinates with comparable noise, the elementary L1 union bound is of order m sqrt(log(m/δ)/n), before any normalization.

## 7. Baselines that answer the question

| Comparator | Purpose |
|---|---|
| Full network | Quality and resource reference |
| Uniform random ranking | Feasible η=0 baseline |
| Magnitude ordering | Simple established pruning rule |
| Taylor/group-saliency ordering | Stronger established pruning rule |
| Greedy calibration-loss universal ordering | Isolate joint multi-budget optimization from local removal |
| Optimized universal law, R=0 | The proposed shared commitment |
| Same model and admissible policy class, R=1 and R=2 | Incremental value of bounded revision |
| Per-budget calibrated mask/law bank | Budget-aware reference; cannot be omitted |
| Slimmable network | Train-once/multi-budget established alternative |
| Separately trained small model(s) | Practical deployment alternative |

Do not compare a band-constrained method against an unconstrained baseline and call the result a fair within-class ranking. Report native methods in the unrestricted track; in a banded track, construct explicitly labeled distributions over their candidate orders using the same feasible-law optimization machinery. Report measured violation and the cost of the transformation. A deterministic importance ordering generally violates the tight band.

For m small, the calibration LP bank is exact relative to its calibration objective. It is not an oracle for the unknown test distribution. A test-set best-subset oracle may be displayed only as a retrospectively labeled diagnostic and must never select deployed configurations.

## 8. Experiment matrix and figures

E1 — **Does the abstraction predict subset damage?** Compare signed mean g, per-sample additive residual, and measured network ablation over held-out subsets at each k. Report absolute/tail approximation error and selection regret, not correlation alone. Separate additive and ordinary networks.

E2 — **What is the price of commitment?** At every k compare universal, repaired and budget-aware methods on test MAE/RMSE and output distortion. Show all budgets, not just a pooled average. Also report the maximum budget regret and average under an explicitly fixed budget distribution.

E3 — **How much does a local revision buy?** R=0,1,2 versus the mask bank. Plot quality versus exchanges and versus actual loading/reconfiguration cost. Report the fraction of commitment gap recovered only where the gap is positively resolved; do not divide by near-zero noisy denominators.

E4 — **Where is balancing justified and costly?** Plot quality against η (or measured m max_{i,k}|p_i(k)-k/m|), alongside an unrestricted comparator. Verify final as well as initial marginals. Do not call η=1 unrestricted for general m.

E5 — **Is there a real resource benefit?** Batch-1 latency and memory at each budget, with deployment artifacts that skip computation. Include model loading and selector overhead where relevant; give separate steady-state and reconfiguration metrics.

E6 — **Does calibration transfer?** Vary calibration sample count, peak/off-peak demand and held-out days. Compare learned policies on fresh periods. Use paired training seeds and temporal-block uncertainty estimates; preserve failed runs and poor regimes. Statistical uncertainty and an LP primal-dual gap are different quantities.

Recommended main empirical figures:

1. Budget–MAE and budget–latency panels, same legend and checkpoints.
2. R=0/1/2/mask-bank quality-versus-reconfiguration frontier.
3. Predicted-versus-actual subset damage plus selection-error panel.
4. η–worst-budget quality frontier, only if balancing has a defensible interpretation.

Calibration sample-size/OOD and per-seed detail can go to the supplement. Existing exact parity/robustness figures remain theoretical evidence, not neural-network performance curves.

## 9. Interactive presentation and optional actual game

First deliver a replay on real held-out traffic: city/sensor map, target future congestion, predicted congestion, compute-budget slider, active modules, measured prediction error, and R=0/1/2 choices. Recompute predictions using trained configurations, or clearly label cached results. The display should reveal the selected groups and the reason a swap changes cancellation/quality. This is interactive forecasting, not a controller claimed to reduce congestion.

For an actual control game, use SUMO through RESCO/LibSignal. Train or obtain one controller, freeze it, and compare its compressed variants using the same observations, traffic demand seeds, phase constraints and action rules. The method remains model compression. A direct small controller and the full controller are comparators. Keep yellow/minimum-green handling identical.

Measure travel time, queue, throughput, missed inference deadlines and unfinished trips. Unfinished trips cannot silently vanish from travel-time averages. If latency is simulated as a control delay, disclose and calibrate that mapping; otherwise report latency as a separate system measurement.

One episode may choose a budget once to match C. Repeated budget switching is a separate empirical stress test: the paper's current one-reveal recourse theorem does not bound a time sequence of reconfigurations. A controller game cannot be inferred to improve from lower forecast error alone.

## 10. Work order and release criterion

1. Freeze the empirical question, exact loss, budget unit, fairness justification and baseline menu.
2. Reproduce one full traffic model; establish chronological splits and resource measurements.
3. Build the m=8 additive model and ordinary-network comparison; train with paired seeds.
4. Export all calibration subset costs and verify ablation implementation against actual skipped execution.
5. Implement full-subset flow, per-budget and common-law recourse LPs; check against permutation enumeration only for tiny m, and verify actual item marginals.
6. Add the cost-table identity and selected-policy transfer statement; mark precisely what is formal versus derived on paper.
7. Run E1–E3 and E5 pilot. If one-swap has no useful held-out gain, or mask banks incur no meaningful extra cost, revise the application claim rather than adding attractive videos.
8. Replicate on a second dataset/architecture, add E4 if operationally meaningful and E6 for calibration robustness.
9. Build the replay from frozen experiment artifacts; add a control game only if it tests a further concrete claim worth the cost.
10. Integrate Experimental Setup and Empirical Results after the theory/method sections. State which parts use actual neural losses, which are exact family theorems, and which are empirical hypotheses.

Suggested future layout, not created by this memo:

    research/paperC_traffic/{configs,manifests,data_splits,checkpoints,subset_costs,policies,results,figures}
    scripts/paperC_traffic/{train,export_costs,solve_policies,evaluate,profile,replay}.py

Each run manifest records dataset/split hashes, checkpoint and producer/dependency hashes, group definitions, seeds, preprocessing, solver status/gap, timing protocol, hardware, and all failures. No fabricated launch commands are supplied before these scripts exist.

A successful extension requires a measurable held-out commitment/repair effect and an honest systems trade-off. It does not require every canonical parity prediction to survive on neural networks. If arbitrary model losses need many swaps, report the empirical repair curve and retain the exact one-swap theorem only on its proved families.
