# MARL — independent recheck after the 13:25 worker update, 28/09/2026

Scope: actual F5 v2 producer and saved full tables; ScoreLocal/score_frontier and SafeEdit Lean statements; current manuscript E3/Limitations; paired-result JSON; selector checkpoint serialization and closed-loop v3; dense/resume scripts and label v3. This is not a whole-repository certification. No new rollouts, training, gate or final test was run. No running producer, ledger, frozen protocol or manuscript was changed.

## Verdict

The F5 corrections are substantive and the repaired reduced-instance bounds check out independently. F2-B is a completed negative development experiment. These advances do not establish an incremental benefit from the legal selector on learned actors. Preserve the method-paper goal while finishing the already motivated dense-label and mixed-profile-actor experiments; do not automatically close the project as analysis-only or open another architecture search.

F6 is not ready: deployment parity, dense analysis, provenance and uncertainty still need closure. Worker understands the broad destination and has implemented many handoff items. Completion of these items, rather than more hypotheses, is now the shortest path.

## 1. Independent F5 check from saved values, without the producer's LP

Inputs: research/marl_budget/e3_bridge_v2_scratch_s3_20260928/{f,rows,manifest}.json and the analogous e3_bridge_v2_bc_s3_20260928 files. Each has 16 states and 256 subset values per state. The sources listed in each manifest match current hashes; this only covers the declared source list, not missing checkpoint/dependency hashes.

For each sender j, compute L_j = min_A [f(A+j)-f(A)] and U_j = max_A [f(A+j)-f(A)]. Direct interval feasibility gives:

    eta_star = max_j (U_j-L_j)/2
    eta_top  = max(eta_star, max_{p in P, q outside P} (U_q-L_p)/2).

At eta_top, choose w_q=U_q-eta_top outside P, and w_p=max(U_p-eta_top, max_q w_q) inside P. All 1,024 marginal constraints and all cut inequalities hold. This independently reproduces both reported LP values at every state. Enumerating the k-sets reproduces d_min, R1/R2 regret and the bound.

Results:
- eta_top = eta_star in 5/16 states per actor.
- All 16/16 states per actor have a valid ScoreLocal + hTop instance at eta_top. Do not abbreviate this as “only 5/16 satisfy the theorem”.
- Nonzero R1 (loss, bound): scratch (5,14); BC (7,23), (2,12), (3,20). Ratios 2.8, 3.286, 6, 6.667. Other R1 cases and all R2 cases have zero geometric loss and bound.
- The scores are fitted after observing the full value table. This is a reduced-object numerical instantiation, not a deployable estimator or a probability certificate for learned score/value errors.

Scope caveat: one receiver varies; other receivers keep the prefix, the receiver is chosen by smallest logit gap, and the target is H=3 continuation. This does not certify geometry, byte slack or candidate coverage for all simultaneous multi-receiver profiles. Write “consistent with an estimation bottleneck on the tested objects”, not “all global loss has been proved to be estimation”.

## 2. What the new results do and do not close

- F2-B JSON supports the reported lack of improvement over the binary head. Do not spend another closed-loop run on this negative arm merely because a runtime can be implemented.
- F2-A scratch privileged-minus-legal CI changes from [0.10,4.49] to [-0.21,4.56] under seed clustering. BC remains positive. A joint-action diagnostic is not complete simulator state or a ceiling on all usable information: the continuation also depends on future states/caches.
- SafeEdit threshold_sharp now states the claimed quantifier over every tau < 2 epsilon and has an explicit witness. This is conditional sharpness, not a bound on a trained critic's epsilon and not evidence that the safe rule improves traffic.
- The current manuscript separates actor competence and selector contribution and describes the reduced bridge. Final submission still needs the pending results, complete uncertainty, frozen test and artifact closure.

## 3. Ordered work package for the worker

### P0 — deployment parity (L-15), before any v3+ closed-loop run

Current closed_loop_v3.py:85 passes string '+inf'/'-inf' to choose; train_v3/v4/v5 serialize those strings. Implement a NEW runtime version, leaving past sources/artifacts intact.

Required behavior:
1. Parse finite numbers and explicit '+inf'/'-inf'; preserve legacy None = -inf only for old checkpoints; reject NaN/unknown forms.
2. +inf always returns the prefix; -inf retains old unrestricted-threshold semantics. Exercise exact tie and no-feasible-edit cases.
3. Support only the chosen deployable feature recipes and fail clearly on unsupported ones. Reject priv_joint checkpoints. If queue bid is a final comparator, implement its receiver-local quantization, normalization and byte charge exactly as training.
4. On saved development inputs, runtime and trainer must agree on features, anchored candidate scores, feasibility, selected index and charged bytes. No simulator rollouts are required for most of this parity check.
5. Then run a short development episode for protocol/access assertions. Never use 1301–1316 for debugging.

No need to implement every failed multi-class model in production unless it is actually selected for evaluation.

### P0 — protect the running label lane (L-10)

Inspect the actual command/log of lane B. If it completes without restart, record completion. If its v2 producer stalls, use a controlled restart of that particular lane with v3 and the ORIGINAL shard count/splits/checkpoint. Do not edit a running shell/producer, broad-kill Python, or start a second writer in its output directory. This is a restart risk, not evidence that all existing labels are wrong.

### P1 — dense labels and F1 (L-12/L-21/L-22/L-31/L-32)

Prepare the analysis runner now; execute only when input shards have completed successfully.

1. Retain the originally registered v2 analysis. The v3 comparison with +inf is an added analysis, not a retroactive replacement endpoint. Record directory/producer deviations separately from the frozen protocol.
2. Evaluate old-label and dense-label models on ONE common development label table. Their candidate families differ even at the same (episode,t), because candidate RNG advances at different snapshot times. State intersection alone is insufficient.
3. For a clean data-density comparison, keep SELECT/tuning data and trainer/threshold recipe fixed. Report the full registered dense train+select+dev recipe separately if it changes these too.
4. Use matched training resources; report actual candidate-label cost and distinct traffic episodes. More adjacent states are not independent new episodes.
5. Run the registered dense acquisition comparison with legal bins and equal actual label count (L-32), or explicitly record it as deferred and narrow the acquisition claim. Do not silently drop it.
6. Report selected gain, harm conditional on edit, oracle regret/headroom, response diagnostics and seed-cluster intervals, with the always-prefix option available in the added v3 analysis.

Resume/provenance closure:
- Preserve partial files. A missing gzip footer alone does not mean valid recovered JSON rows are wrong.
- Current v3 catches EOFError/OSError and silently keeps the last duplicate (episode,t). It does NOT establish “no line lost/conflicted”. Check exact expected keys by split/shard/snaps, missing/extraneous keys, duplicate canonical JSON hashes and parse-error offsets.
- Compare recovered complete records semantically (canonical JSON/array values), not compressed gzip bytes: headers/compression can differ without label changes.
- Record per-part producer provenance and checkpoint identity. If original provenance is unknown, mark that explicitly. Inspect prior logs for failed self-checks: v3 resets failures=[] and does not revalidate recovered lines.
- A small deterministic replay validates sampled paths, not every saved record. If a mismatched/conflicting row is found, regenerate the affected keys with one declared producer/checkpoint before use.

### P1 — clustered uncertainty and seed declaration (L-16/L-25)

Recompute delay, message-use and closed-loop intervals from raw rows, preserving both loads within a traffic-seed cluster and pairing methods. Report actor seeds separately; selector initialization seeds are not independent actor replications. At final aggregation reflect both actor and traffic variation.

Declare added actor seeds 3/4 in a NEW dated deviation note. Early launch rules out choosing those launch seeds after these outcomes; it does not rule out subsequent selective reporting/stopping/checkpoint choices. Include all completed and failed seeds and the original recipe-level/per-seed G1 rule. Do not backdate an amendment or call BC post-gate results confirmatory.

### P2 — finish the bounded development decision

Wait for the already-running dense and mixed-profile actor experiments and remaining actor seeds. Evaluate all methods on the same frozen actor and resource rule; changing actor competence alone is not selector benefit. If a grounded improvement appears, require development closed-loop confirmation before freeze. If none appears, report that method-scope evidence is still missing and ask the author/advisor to choose submission scope; do not manufacture a win or automatically abandon CityFlow.

### P3 — freeze, final evaluation, manuscript

Freeze exact checkpoints/hashes, inference versions, candidates, thresholds, absolute resource accounting, comparators, actor-seed inclusion, primary endpoint, practical margin, uncertainty and guardrails BEFORE opening seeds 1301–1316. CI containing zero is not equivalence. Freeze must precede the test, not merely reserve seed numbers.

Then execute the fixed final panel, report all endpoints/failures, update the figures and claim map, remove TODOs, compile and visually inspect the actual submission PDF, package the minimal reproducible commands and provenance. Venue/track/format remains an author/advisor confirmation; it does not block completing the scientific content.

## 4. Destination and novelty boundary

The intended contribution remains a concrete communication problem with a commitment/revision theory, a legal algorithm, and learned multi-agent traffic evaluation. The exact theoretical mechanism may be valuable without successful selectors, but it does not convert into a demonstrated MARL method advantage by counting gated theorems or by showing MAPPO beats MP2. No new literature priority claim is made in this audit.

The full handoff remains MARL_FINISH_HANDOFF_20260928.md. This note narrows its remaining tasks using the new evidence; it does not change the target or authorize extra heavy experiments.
