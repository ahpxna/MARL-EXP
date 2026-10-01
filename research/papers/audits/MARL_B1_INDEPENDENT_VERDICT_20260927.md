# B1 independent verdict — 27 September 2026

## Decision

B1 FAIL is supported. It does not prove an information-theoretic impossibility for legal selectors, and it does not guarantee that a small fresh bid closes the gap. Keep the numerical decision rule; correct the causal interpretation separately without altering the frozen protocol.

## What was independently checked

- Complete collector and trainer source; v2 learner/selection definitions, previously audited.
- All 40 distinct jobs completed; runtime 4776.87 seconds.
- Five training source hashes match current files. Collector/replay manifest producer hashes also match.
- Reconstructed all 384 test groups from the four raw label shards, including per-receiver prefix masks, the actual byte cost function, radius constraints and oracle gain at +28B.
- For every job, recomputed oracle gains agree with the report; each saved selected gain is attainable among its stored candidate values. Reaggregation of saved per-group gains agrees with summaries.
- LIMIT: the B1 driver discards trained model blobs and does not save chosen indices or predictions. Unlike diagnostic v2, this artifact does not permit an independent replay of every selector choice or direct verification of its selected profile's legality. Attainability of a gain is weaker than replay of the choice. No claim of full model replay is made.
- A sensitivity bootstrap clustering the two loads of each traffic seed together (8 clusters, 10000 resamples) preserves the main legal-primary/privileged-reference conclusion. This is supplementary, not a replacement for the preregistered 16-episode endpoint.

## Results at N=64, cap +28B

| Method | Mean gain | Registered CI95 | Fraction of oracle |
|---|---:|---:|---:|
| PRIMARY history MLP | 0.19271 | [-0.35072, 0.75000] | 1.446% |
| Public MLP | 0.61892 | [0.00777, 1.29167] | 4.643% |
| Ridge/history | 0.75521 | [-0.04688, 1.57038] | 5.665% |
| Privileged joint-action MLP | 8.81944 | [5.77344, 12.09377] | 66.159% |
| Oracle over stored R1 candidates | 13.33073 | reference | 100% |

History initialization gains are +0.72396, -0.05729 and -0.08854. All three primary conditions fail. It cannot be rescued by choosing N=32 after seeing test results or by changing the primary to public MLP. Nevertheless public MLP has a small positive registered interval; claiming every legal method is completely unable to learn is also wrong. Its practical value requires a resource/traffic interpretation, not just percentage of oracle headroom.

## Corrections to the worker's interpretation

1. Replace “not a data-scale failure / information bottleneck confirmed” with: “Increasing the training seed pool from 8 to 64 did not close the gap for these learner/representation/selection choices; giving counterfactual joint actions substantially improved prediction and selection.” The latter supports an actor-response hypothesis but does not identify its causal mechanism. Different inputs change both information and representational difficulty. No Bayes-risk bound, indistinguishable legal-history witness, or consistent-estimator limit is established.
2. A protocol can preregister a decision rule. Preregistration cannot make a logically stronger causal interpretation valid. Preserve the protocol byte-for-byte; add an interpretive correction in the results/audit.
3. In the user-facing message, 12–29% was described as action changes “per edit.” Code reports action changes per ALL groups. Conditional on editing, history is 25.3–32.8%, public 22.7–32.8%, privileged joint-only 98.7–100%. The markdown table already uses the per-group denominator; label it explicitly. This correction does not reverse the result.
4. Privileged +8.82 is not an achievable target promised to a 1-byte bid. That reference receives candidate-dependent counterfactual joint actions, not just one currently intended action per agent.
5. The strongest direct comparator has not been independently tuned: direct shares a critic whose epoch/lambda was selected for repair_R1, although it gets its own threshold. Keep the shared-critic label. No unique advantage of revision over budget-aware selection is shown.
6. These are offline candidate-set results on frozen MP2 / H=3, not successful learned closed-loop MARL. The oracle is over the stored candidate set, not all byte-feasible profiles.

## B2: a defensible bounded next question, not an automatic new training campaign

If separately authorized, first fix the information and byte contract before collecting more traffic:

1. Define each bid b_i=enc(local observation_i, already-paid receiver cache_i, known public variables). State whether K is already known, message timing and whether encoding is fixed or trained on training data only.
2. The encoder must not access fresh payloads from other agents, the true counterfactual joint-action table, future rollout values or hidden labels. A request/reply round must include its communication/time cost. One action under the current prefix is not an answer for every possible patched profile.
3. Charge bid payload AND control overhead within the SAME total +28B budget. Filtering candidate profiles must use the resulting remaining budget; “+28B patches plus free bids” is a different task.
4. Use existing development artifacts to test whether the proposed locally computable bid predicts actor changes and improves selection. Compare no-bid, this bid, a simple same-byte queue bid, and a direct budget-aware selector with identical bid access. Privileged joint actions stay only a reference. Select the encoder and thresholds without using the now-open B1 test as a new sealed test.
5. Only if that bounded development check is useful should a fresh confirmatory panel be registered and run. Measure actual gains, harm, bytes and action changes; predicting actions alone is not the final objective.

This is a concrete way to examine B2 cheaply, not evidence that it will succeed. Do not automatically start actor training, a new simulator, or a larger architecture search. Existing negative data remains useful if B2 is unhelpful.

## Submission positioning and gate

Current supported package: revision geometry and calibration analysis, controlled examples with explicitly stated channels, plus an oracle/negative-learning traffic diagnostic. This can be developed as an analysis-oriented communication paper; neither novelty nor publishability follows merely from that label. The E1b raw-reward/Gaussian-channel mismatch documented in MARL_E1_INDEPENDENT_AUDIT_20260927.md must be resolved or explicitly separated first.

The existing A/B/C and older functional-margin/drift assets remain useful. They are not evidence that a fresh-bid learner works. Do not force a successful-MARL claim into this submission.

Verified gate17 SUMMARY: 146/146, 1298 audited theorems, zero failed/sorry/native_decide, standard axioms, SMOKE PASS at21:54:04. Gate4 was still running, 8 completed exit files all0 at the final check. No running gate was edited and no new experiment was launched.

## Artifact limitation to fix before any future expensive training

Save a frozen source manifest at start, per-job checkpoint/result/model/prediction artifacts atomically, and periodic progress. The B1 driver writes the final report only after all jobs and discards model blobs. Four workers each reconstruct the full dataset; the observed swapping means a future run should share/precompute arrays and benchmark concurrency before assuming four workers are faster. No rerun is required just to preserve the present negative conclusion.
