# Independent audit of the completed heterogeneous learner diagnostic

## Decision

The replay is complete and its mirror construction fixes the legal-history omission identified in the previous audit. The reported aggregate gains reproduce. No successful deployable learned selector has been demonstrated. Do not expand simulator collection or actor training on this evidence.

However, the diagnostic has not completed the promised selection of a no-edit threshold. Its handling of the zero-gain reference and ties needs correction before describing it as a conclusive test of selective revision. This does not promise a positive result after correction, and does not justify another broad research branch.

## Evidence inspected

Read the entire receiver-mirror class, environment subclass, replay script, diagnostic trainer, mirror tests, worker result document and analysis script. Independently inspected the replay manifest, joined labels and joint actions, and diagnostic report. No new simulator rollout, training or Lean compilation was launched. A tiny synthetic check executed the actual `select_eval` function extracted from its source.

Paths relative to the project:

- `models/marl_receiver_mirror.py`
- `envs/external/cityflow_hetero_mirror.py`
- `scripts/MARL_hetero_mirror_replay.py`
- `scripts/MARL_hetero_diag_train.py`
- `tests/test_marl_receiver_mirror.py`
- `research/marl_budget/HETERO_DIAGNOSTIC_RESULTS_20260927.md`
- `research/marl_budget/hetero_pilot_20260927_181207/{labels,mirror_diag,diag}/`

Replay is COMPLETE: 120 unique snapshots, 24.61 s. Labels and mirror hashes match the manifest. Every recorded replay and trainer source hash matches current source. Diagnostic is COMPLETE: 319.88 s, 288 fit groups, 96 inner-selection groups, 96 validation groups. These are 72/24/24 snapshots with four K vectors each, not that many independent traffic episodes. Seeds are 41–48 and 51–52 only. Joined per-group candidate/joint-action counts match. Stored phase IDs are 1–8, so the current modulo-eight one-hot mapping is injective on these data.

The replay code asserts original z/order/live K equality, two re-rolled stored values at every snapshot, no mutation of the live fingerprint, and mirror/cache equality after every transmission. This is meaningful replay evidence; it does not independently reroll every stored label. The 5 mirror tests were read, not rerun for this audit.

## Numerical results verified at +28 B

| Predictor | Mean R1 gain, range across initialisation seeds |
|---|---:|
| public MLP | -1.365 to -0.208 |
| public + legal receiver history | -0.875 to +0.312 |
| interaction ridge, public/history | -1.125 / -1.281 |
| privileged current summaries + joint actions | +6.417 to +7.188 |

All predictors use identical candidate oracle references. The +14.59 oracle is over the stored candidate set, not the complete R1 family. There are 150–210 candidates per group (mean 181.12).

Privileged gains are uneven by load: headway 8 gives +12.33 to +13.27, headway 16 gives +0.50 to +1.48. Four validation episodes are two traffic seed IDs under two loads, not four independent seeds. This is a useful positive control with limited breadth.

## Required corrections

### 1. Zero reference and tie handling

At `select_eval`, lines 133–137, the algorithm maximises raw predicted gain including a learned prediction for the prefix, then compares the winning score to absolute zero. It does not enforce Delta_hat(P)=0 or prefer the prefix when it is tied for best. A learned prefix prediction need not equal zero despite its training label being zero. The ridge centring also makes its raw-zero feature vector map to a nonzero prediction.

Synthetic reproduction using the actual function: two feasible candidates [edit, prefix], true gains [-5, 0], predicted scores [0.2, 0.2]. The function chooses the harmful edit, spending 28 extra bytes. Predictions [-0.1, -0.2] choose the prefix, while adding the same constant to both scores to get [0.1, 0] chooses the edit. Thus the absolute-zero rule is sensitive to an unanchored reference.

For the intended anchored-gain policy, use scores relative to the prefix (or a model parameterisation guaranteeing zero at the prefix), set the prefix score exactly to zero, and prefer it whenever improvement is within a declared tolerance. This changes the policy and must be versioned; do not overwrite the old report.

### 2. The claimed threshold selection was not implemented

`train_mlp` and `fit_ridge` select epoch/lambda on inner-selection seeds, but `select_eval` uses only the fixed threshold zero. There is no threshold sweep and no never-edit policy in model selection. The report's sentence “model and threshold selection” is incorrect.

For one bounded correction, select a nonnegative no-edit threshold on seeds 47–48, with an explicit never-edit option. Use the same rule for repair and direct selection. Declare whether selection targets the +28 B operating point or a fixed combination of caps; the current checkpoint objective is uncapped only. Report actual gain, edit rate, harmful edits (denominator stated), and bytes. Do not tune on validation 51–52 or test 61–64.

### 3. Ridge diagnosis overstates what was measured

Selecting lambda=10000 at the grid edge does not establish that predictions are constant, that ties caused all edits, or that a wider grid can only converge to never-edit. Finite positive rescaling can leave rankings and sign unchanged. No margins, coefficients, candidate predictions or fitted models were saved to establish the proposed explanation. The synthetic tie bug is real, but its incidence in the actual ridge output is currently unknown.

### 4. Privileged control does not isolate action prediction

The control changes both current-state summaries and candidate/baseline joint-action features. It demonstrates that this combined privileged representation supports useful ranking on this validation panel. It does not identify action prediction as the unique causal bottleneck, prove legal information insufficient, or prove that fresh bids solve it. Earlier privileged-summary pilots used a different objective/selection/evaluation and are not a matched ablation for this control.

Retain the result but replace “identifies action prediction as the barrier” with “supports actor-response prediction as one candidate bottleneck”. At a fixed snapshot f_x(S)=Q_H(x,a_x(S)); Q_H still depends on x across snapshots.

### 5. Scope of the negative result

This run uses stored candidate-set argmax, not the previous deployed coordinate search. MLP uses only 72 fit contexts after inner splitting. Validation 51–52 was already used in previous development; the new internal split does not make it a fresh confirmatory panel. No training seed here is a learned-actor seed. Do not promote the result to a general information-theoretic impossibility or an empirically successful MARL method.

Across all stored non-prefix labels, approximately 60.7% train and 60.2% validation gains are exactly zero; 58.8%/58.7% induce the same joint action as the prefix. These are candidate-weighted descriptive statistics, not selected-policy rates. This also makes “edits frequently” different from “changes the executed action frequently”.

## Minimal worker task

Preserve existing code/report for provenance. Implement a versioned selection diagnostic with anchored prefix scores, deterministic prefix-favouring ties, and an inner-selected no-edit threshold including never-edit. Save selected model/normalisation, epoch/lambda/threshold, candidate predictions and chosen indices. Existing labels and mirror features suffice; no new traffic collection is needed. Since the old trainer saved only aggregate episode metrics and no model/predictions, this cannot be faithfully repaired by editing its JSON: the bounded fit must be rerun if the experiment is continued.

This correction can complete the already-promised diagnostic; it is not authorisation to enlarge data, buy bids, train actors or change simulators. If it remains unhelpful, stop the current learned-traffic expansion. Stopping now for submission-resource reasons is also defensible, provided the limitations of this diagnostic are recorded accurately.
