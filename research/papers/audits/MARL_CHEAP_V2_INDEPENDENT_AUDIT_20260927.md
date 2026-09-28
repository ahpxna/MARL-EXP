# Independent audit of cheap checks v2 — 27 September 2026

This is a separate audit, not a ledger update. Historical source, data and reports are preserved. No experiment was rerun and no actor was trained for this audit. Computation was limited to reaggregating existing JSON/gzip data and checking provenance.

## Decision

The present evidence does not support a latency, unseen-budget generalisation, or learned-quality advantage for prepared priority plus revision in PROTOCOL_v1. Retire those empirical claims for this protocol. This does not invalidate the abstract revision theorems or the independent A/B/C results.

Do NOT promote the heterogeneous-receiver result to a demonstrated bounded-revision benefit, and do NOT treat 1,000 contexts as a decisive test of learnability. First repair the experiment-to-claim mapping. A large learner run on the old global-budget objective would not test the proposed heterogeneous-stream mechanism.

## Evidence actually inspected

Read in full:
- `scripts/MARL_cheap_checks_v2.py` (200 lines).
- `scripts/MARL_cheap_checks_v2_train.py` (216 lines).
- `research/marl_budget/CHEAP_CHECKS_V2_RESULTS_20260927.md`.

Also inspected the imported MP2 actor, subset-table producer, network/training implementation, broadcast adapter, and base environment's counterfactual views, summaries, caching and rollout value.

Artifacts inspected:
- `research/marl_budget/cheap_checks_v2_20260927_171810/data/manifest.json`.
- All 192 records in `data/tables.jsonl.gz`.
- `models/report.json`.

Verified:
- Table SHA256: `0f812364d837e60094f461216df451e77e02fef6e62dea75f1831071d7e3abd2`; equals both manifest and model-report references.
- All seven source hashes recorded by the collector match current files.
- 192 distinct episode/time records: 96 train, 48 validation, 48 test.
- Training traffic seed IDs: 11–14; validation: 21–22; test: 31–32, each at two loads. Three network initialisations do not create additional independent traffic test seeds.
- Collection: 305.42 seconds; training: 106.73 seconds.
- The trainer report contains no trainer/dependency source hashes. Its numerical summaries can be checked, but current trainer source cannot be cryptographically identified as the exact historical producer. No checkpoints or per-context learned selections are saved there. This limits retrospective analysis; it is not evidence of fabricated results.

## 1. Check 4 optimises AFTER receiver budgets are known

Collector lines 59, 73–95: `kr` is sampled first; `shared_joint(order)` uses that same realised vector; local search then optimises the order against it. One vector is sampled per snapshot.

This is a valid diagnostic for a shared order with known heterogeneous receiver budgets. It is NOT an experiment for an order committed before an unknown budget is revealed. Those are different objectives:

- budget-aware order: E_K[max_pi f_x(pi,K)];
- order prepared before the reveal: max_pi E_K[f_x(pi,K)] (or a specified worst-budget objective).

Fix for the next producer: explicitly define the timing. For the advance-order claim, choose one order using a training distribution of receiver budgets, freeze it, and evaluate it on separate revealed vectors. Never reoptimise the base order on each evaluation vector. Report the known-budget oracle separately.

The current packet rule also skips the receiver's own packet before taking its first k_i OTHER packets. Thus k_i is a fresh-other-packet capacity, not necessarily a stopping slot in the common stream. Either retain and name that model, or use stream-slot limits and charge self-packet slots consistently.

## 2. The +4.81 is NOT a bounded-revision result or a certified optimality gap

Collector lines 97–112 enumerate every subset of the receiver's permitted size, collapse them to achievable actor actions, and perform coordinate ascent over those actions. There is no R, no distance from a prefix, no patch-byte limit, and no transmission implementation. The final private subsets are not saved.

Reaggregation confirms:
- best-found shared order minus heuristic: 26.0260417;
- best-found private profile minus best-found shared order: 4.8072917;
- private improvement positive at 95/192 snapshots (49.48%).

Because both optimisations are heuristic, the difference is neither a lower nor an upper bound on the difference between their optima. The shared search could simply have missed an order attaining the private profile's value. A positive found improvement does not prove a structural price of sharing.

Likewise, 4.81 is neither a cap on what revision could gain nor evidence that R=1 gains this amount. The correct description is: an unrestricted private-profile search found that improvement over this particular shared-search incumbent.

Required next quantities:
1. A shared-order optimum or an upper/lower certificate interval.
2. For the SAME frozen base order and revealed budgets, feasible profiles with per-receiver R=0,1,2, plus unrestricted private profiles.
3. Save the actual selected subsets and verify |S_i|=k_i and |S_i\P_i|<=R.
4. Charge patch/control traffic. Discarding a packet already received does not refund transmitted bytes or listening time.

Small exact diagnostic is plausible: for this m=9 panel the largest product of per-receiver achievable-action counts is only 2,592. Enumerating 9! orders and deduplicating their joint actions can certify the shared optimum on a small preregistered subset of snapshots. Enumerating the Cartesian product of achievable actions can certify the independent optimum. Cache each distinct joint-action rollout. Runtime is not yet measured; do not promise this is free or launch all 192 by default.

This diagnostic remains oracle-only. It measures whether the proposed mechanism exists before attempting to learn it.

## 3. The 53%/10% denominator comes from a different feasible family

The 49.5670573 denominator is the mean spread across homogeneous GLOBAL k-subsets, averaged over k=1..8 and snapshots. Check 4 uses heterogeneous receiver profiles with k_i=1..7. Those feasible families differ.

Using 49.6 as an explicitly labelled reference scale is arithmetically legitimate. Calling 4.81/49.6 the fraction of available heterogeneous-repair benefit is not.

Use raw waiting-value differences first. If normalising, compute a range or comparator improvement for the SAME heterogeneous objective and budget vector, with certified/best-found status explicit.

The rollout value is minus the SUM of waiting counts at three decision boundaries, with phases held throughout. A gain of 26 is not automatically 26 unique cars, a throughput improvement, or a 53% reduction in travel delay.

## 4. Fresh bids are described as charged, but not accounted for in the implementation

Collector lines 153–163 obtain oracle payloads and extract clipped one-byte waiting totals. The live segment at 164–172 only sends the old global selected set. It does not send bids, add 9 bytes, debit a shared budget, or record bid/control latency. Trainer lines 47–55 simply concatenate bid features.

The present result is an OFFLINE ablation granting fresh quantised local-summary information. It is not a matched-byte comparison of a paid-bid algorithm. This is a concrete reporting/accounting mismatch; the values themselves remain useful diagnostic data.

Fix: either label the diagnostic correctly now, or implement bid transport and include all m bids plus framing/control costs. Compare at the same total network bytes, or show quality-versus-total-byte curves. If bids are physically broadcast to actors too, specify whether actors can use them; do not silently grant or hide additional information relative to the declared protocol.

## 5. “Ceiling” is not a full-state information ceiling

Collector lines 44–53 and 161: fresh features contain phase, phase duration, approach-level vehicle totals and waiting totals. They omit vehicle positions, route/arrival details and other simulator state relevant to the held-phase rollout. They are privileged CURRENT SUMMARIES, not a sufficient statistic for the true value table.

Observed train/test gap is real. Its cause is unresolved. It could involve limited independent contexts, architecture/optimisation, distribution shift, missing predictive features, or a combination. Low train error and high test error do not isolate data scarcity as the cause, and failure after 1,000 contexts would not prove that selection is unlearnable at a useful scale.

Rename the condition `privileged_current_summaries`, retaining the historical `ceiling` key as an alias if necessary. Any claim of an information ceiling needs a sufficiency argument for the target, not just fresh observations from all intersections.

The test set has four episodes but only two traffic seed IDs. Do not infer statistical equivalence from close aggregate means or call differences “noise” without a paired episode/seed analysis.

## 6. Unseen-budget implementation is improved, but has a small remaining label-access defect

Good changes verified:
- Critic losses only use within-layer centred labels at trained k.
- Direct policy only trains at trained k.
- Singleton-score method is omitted in the holdout regime.
- Checkpoint selection uses validation decision regret at training budgets.

Remaining issue, trainer lines 114–116:
`delta = Y - Y[:, [0]]; scale = delta[tr].std()` uses ALL subset-size columns, including held-out k, to set target scale. For the current data that scale is 22.9936561; merely restricting its columns to trained k changes it to 22.8464833. This is limited aggregate label access, not evidence that it explains the negative result, but “no held-out-budget supervision” is not literally true.

Fix: compute training-budget within-layer centred targets first, derive scale from those training labels only, and use those same centred targets for both critic and direct losses. A per-layer additive target constant does not alter the within-layer optimum. Add a test that modifying every excluded-budget label leaves training normalisation, losses and learned outputs unchanged under a fixed seed.

Comparison caveat: public 6.70 (all-k training, all-k evaluation) versus 7.39 (even-k training, odd-k evaluation) changes BOTH the training and evaluation domains. To measure degradation caused by withholding budgets, evaluate both trained models on exactly the same k=3,5,7 records.

The table supports no observed priority advantage for the tested models. It does not establish a universal advantage of budget-conditioned networks.

## 7. Similar mean regrets do not prove identical policies or zero nesting cost

The three critic-based methods are close in mean true regret. The largest reported mean spread is actually 0.324074 (ceiling/holdout/test), slightly above the report's “within 0.3”. This rounding issue is minor.

The consequential issue is that similar means do not establish per-context equality, no tail penalty, or no benefit at any budget. The critic can assign inaccurate values to several distinct sets whose actual regret averages happen to agree.

Report per-k and per-episode paired differences, selected-set disagreement, and worst-budget regret. The dynamic programme in `chain_from` minimises SUM of predicted regrets across k, not maximum regret across k. Do not present it as the paper's minimax all-budget solver without changing that objective.

The current trainer saves aggregate means only; a follow-up should save (episode, time, seed, feature condition, regime, k, selected set, realised value) so these comparisons do not require retraining.

## 8. Full communication being worse is a fixed-actor result

Verified mean full-minus-none: 5.4635417; episode means range from -11.5833333 to +19.4166667.

MP2 mechanically incorporates received downstream waiting counts; it is not an optimised decoder with an option to ignore every additional message. Its full-information value can therefore decrease. A theorem that maximises over decoders and permits ignoring messages may still be monotone, but it concerns a different objective from these f(S) tables. This realization gap matters for the planned communication theorem.

## Work order toward a submission

### Step 1 — Correct claims without changing historical evidence

Use: “no demonstrated priority/revision advantage in this offline panel.”
Do not use: “information rule ruled out”, “data scarcity proved”, “R=1 has 10% headroom”, “1,000 contexts settles learnability”, or “nesting costs zero”.

Retire the latency-advantage story for PROTOCOL_v1. Keep the tabulation result and negative panel as an honest diagnostic, not as support for the intended positive claim.

### Step 2 — Choose and test the actual mechanism before training at scale

If the candidate is one physical broadcast stream with receiver-specific stopping limits, write that timing and cost model explicitly. Keep shared order preparation, reveal, bounded patching and actor actions separate. Test the controlled R frontier on a small balanced set of snapshots chosen before inspecting their gain. Include an exact/certified shared comparator. If a structural R benefit is absent or disappears at equal byte cost, do not spend actor-training time trying to rescue that mechanism.

### Step 3 — Only if Step 2 supports the mechanism, run a learning curve on THAT objective

Do not scale the homogeneous-global-subset learner and call it a heterogeneous-stream experiment. New labels and model outputs must represent the selected mechanism.

Compare fixed heuristic, learned shared order, shared order plus bounded repair, and a direct budget-aware comparator using the same legal information and total cost. Include a privileged-summary diagnostic separately.

Use nested training datasets such as 96/192/384/768 contexts drawn from MORE independent traffic seeds, not just denser sampling of the old trajectories. Freeze validation and keep a new untouched test panel: the old test results have already guided design choices. Include simple regularised learners and an action-informed baseline before increasing network complexity. Select hyperparameters on validation only and save raw decisions/checkpoints/source hashes.

Use the learning curve, paired improvements, cost and runtime to make a project decision under the deadline. A chosen cutoff is a resource decision, not a theorem of impossibility.

### Step 4 — Make the MARL claim only after a learned actor and closed-loop evaluation

Current MP2 is a hand-designed frozen controller. Selector fitting alone is not evidence of learned multi-agent coordination. Once mechanism and learnability pass, evaluate with learned actors and new traffic seeds under closed-loop rollouts, accounting for bytes, waiting/delay, throughput and any deadline failures. Keep the H=3 offline table experiment as a diagnostic, not the primary claim of improved traffic control.

## Recommendation

Do not launch the proposed blind 10x rerun yet. The smallest decision-relevant next job is the matched-protocol, bounded-R oracle comparison in Step 2, with the light holdout/recording fixes from Step 1. It tests whether there is a positive mechanism worth learning. A/B/C assets remain useful, but this MARL application currently has no validated performance advantage.
