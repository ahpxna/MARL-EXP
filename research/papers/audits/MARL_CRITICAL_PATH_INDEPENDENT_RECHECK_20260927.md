# Independent critical-path recheck — 27 September 2026

Scope: read the complete submission critical path and status document, the pasted B1 report, B2/B3/B5/B6 reports and relevant producers. Inspected process state, run manifests and saved result arrays. No experiment rerun, actor training, producer edit, ledger edit, or interruption of a running worker.

## What the worker has actually completed

| Original critical-path step | Current evidence |
|---|---|
| 1. Protocol and joint measurement | Implemented for the explicitly different heterogeneous-receiver broadcast protocol. Joint restricted-view evaluation, paid bids, saved profiles and mirror checks exist. The new baseline below still violates its stated bid contract. |
| 2. Learned communication-aware actor | NOT DONE. The inspected live runners still call mp2_action. B4 trains the selector/response model, not an actor. This remains necessary for the intended learned-MARL submission. |
| 3. Evaluator, selectors and strong comparisons | PARTIAL. B2 held-phase confirmation passes; B3 closed-loop confirmation fails. B4 and separately tuned direct scorers are in progress. New communication baselines are heuristics, not trained SchedNet or Where2comm reproductions. |
| 4. Controlled calibration | Experiments and formal results exist, with the previously required separation between Gaussian theory and executable E1b reward channel. These do not certify traffic sample complexity. |
| 5. Main learned-MARL experiments | NOT DONE. Frozen-MP2 load/capacity panels exist; learned actor seeds, matched learned baselines, acquisition ablation and end-to-end delay remain. |
| 6. Submission | NOT DONE. Existing theoretical/controlled figures are assets; the current status document says MARL manuscript not started and main traffic figure is old. |

Snapshot during this audit:
- B4 on-policy labels and top2_joint training COMPLETE; controls RUNNING; no cl_dev/cl_test rows yet.
- Stage A v2 dev screen COMPLETE (391.36 seconds). Select action accuracy 0.71733 versus always-p1 0.70930; this is a small dev classification difference, not a fresh closed-loop result.
- Baseline panel had 238/320 method-episode rows, no COMPLETE manifest; no partial-panel win inferred.
- Independently tuned direct: no-bid had 1/3 job files, top-2-bid had 2/3, neither complete at the snapshot.
- Four heavy Python processes were observed. A running process or file count does not establish a result.

## Numerical checks

Recomputed B2 and B5 means from all three saved per-group gain arrays:
- B2: method means 3.89973958, 2.98177083, 2.47916667; mean advantage over ctrl_history = 1.84592014, exactly the saved verdict. Reported CI [0.95139, 2.84293], PASS.
- B5: means 1.29947917, 1.59375, 1.19010417; advantage = 1.02430556, exactly the saved verdict. Reported CI [-0.04210, 2.13499], FAIL. Closeness to zero does not change the registered decision.
- B2/B5 recorded producer hashes match current sources. B3 recorded hashes also match.
- B6: positive relative effects on heavy/light load panels do not establish robustness at every new load; load_12 is negative in point estimate. Fixed/bursty/low capacity panels do not confirm transfer. These are descriptive held-phase results, not closed-loop robustness.
- Latency JSON: scheduler median 16.56 ms, p95 17.85, max 47.98; measured bid-compute plus scheduler median 16.97 ms, max 48.35, over 208 steps. Network uplink latency is excluded. Thus observed 0% misses at 50 ms is not an end-to-end 50 ms guarantee.

B2's frozen winning policy is direct at +84B, with an unrestricted stored candidate family and a shared critic. This confirms a paid-bid selector benefit under its protocol, not a distinct benefit of bounded R1 revision over independently optimized direct selection.

## Findings requiring correction

### 1. η traffic bridge is not closed

scripts/MARL_hetero_eta_bridge.py:4–12, 64–76 fits additive scores only to single-receiver one-swaps around P. Its docstring correctly calls t/2 a LOWER bound for global ScoreLocal η, but then calls the fitted margin test a certificate and writes frac_zero_price_certified.

A lower bound cannot discharge the global upper-error hypothesis. The reported 75.7% zero residual does not mean true interaction is zero, and 63.3% passing the fitted cut does not certify global zero price.

Counterexample: m=4, k=2, P={0,1}, f(S)=1 if {2,3} is contained in S and 0 otherwise. All four one-swaps from P have gain zero, so fitted w=0, η_fit=0 passes margin >= 2η_fit. Yet replacing both items gives gain 1. This is a monotone value function.

Required: keep this as an oracle diagnostic named one-swap additive residual / fitted local no-improvement condition. An actual T1 bridge requires a valid upper bound for a single consistent score vector over the relevant contexts and sets, or a theorem explicitly restricted to the inspected neighborhood. For the observed one-swap family, directly checking max gain <= 0 already gives the local statement.

### 2. New request baseline leaks unencoded gap precision

scripts/MARL_hetero_closed_loop_v3.py:59–70 obtains g=gap_of(sc) and sorts receivers by exact g. The declared bid contains p1, p2 and a two-bit gapbin, not the exact gap. Existing bid records contain distinct true gaps within one bin (e.g. 0, 1/6, 1/4, 1/2), so the ranking cannot generally be reconstructed from that bid.

Required after the frozen running producer finishes: create a corrected producer that sorts by transmitted gapbin then a public deterministic tie rule, or charge and expose a richer gap message to all comparators. Re-evaluate the affected request-baseline rows. Do not silently edit the currently running source. Current request-baseline rows are not evidence of an equal-information one-byte comparison.

### 3. Baseline identity is narrower than the names suggest

The v3 source explicitly describes schednet_fresh as hand-designed fresh-queue weights and where2comm_top2 as a nonlearned request rule. They are useful heuristic controls. They do not complete the planned comparison against a learned SchedNet adaptation and cannot support a statement that the proposed method beats the original published algorithms.

### 4. Stage A v2 is still development-only and needs a runtime bridge

The new dev wrapper appends four features (27 inputs); the current closed-loop v2/v3 loader and soft_live construct 23-input stage A. A v2 checkpoint cannot be deployed by pointing the old runner at it. Add a new compatible inference path and train/runtime parity check before any new test. Keep B4's existing v1 checkpoints and producer frozen.

The dev manifest records imported sources but omits the v2 wrapper and coefficient JSON. Similarly, the independently tuned direct wrapper is omitted from its inherited producer list. Preserve hashes of those behavior-changing wrappers/configuration assets in a separate manifest; do not rewrite existing run manifests.

## What is genuinely dropped versus simply unfinished

Withdraw: the measured latency advantage of prepared priority under PROTOCOL_v1; generic budget-generalization superiority not observed; certified neural no-repair without coverage; universal inability to learn from legal information; E1b as the Gaussian pair-channel instantiation; a universal claim that increasing revision rights must increase optimal learning cost.

Reframe: global common budget -> one broadcast stream with heterogeneous receiver capacities; exact traffic enumeration -> explicitly restricted candidate search; topology transfer -> currently only load/capacity diagnostics (fixed-size architecture limitation, not evidence that transfer is impossible).

NOT dropped: CityFlow, learned actors, strong direct baselines, closed-loop evaluation, multi-seed learned-MARL experiments, manuscript. These are outstanding work. Gate and extra calibration theorems do not replace them.

## Next actions towards the intended submission

1. Finish the already-running B4 and direct comparisons; preserve the registered endpoints even if negative.
2. Correct the request baseline, baseline labels and η interpretation before using the panel in a paper.
3. If proceeding to the original MARL scope, implement and train the communication-aware actor; freeze common actor checkpoints for fair selector comparisons. A B4 win supports proceeding but does not itself complete this step.
4. Evaluate matched learned baselines and acquisition under the same byte accounting, with actual delay scope stated. Report any distribution-shift failures.
5. Assemble the manuscript now around supported theory and protocols, with empirical result slots explicitly pending. Do not invent successful-MARL results, and do not postpone writing for optional extra theorems.

No current result forces abandonment of CityFlow. The current evidence also does not establish a finished learned-MARL method.
