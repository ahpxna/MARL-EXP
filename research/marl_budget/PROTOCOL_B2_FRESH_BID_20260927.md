# PROTOCOL B2 — receiver-local fresh bids, charged inside the same byte cap (preregistered)

- **Written** 27/09/2026 ~22:20, BEFORE the fresh confirmation panel exists and before the
  development screen finished.
- **Authorisation:** the user, "làm B2 đi, chuẩn bị mọi thứ để chạy B2".
- **Requirements followed:** MARL_B1_INDEPENDENT_VERDICT_20260927 §B2 items 1–5.
- The body is not edited after data. The design freeze (§5) is appended ONCE, before any
  confirmation label is collected.
- No ledger is edited.

## 1. Question

B1 showed that legal-history selectors capture only 1–5% of the oracle R1 headroom. The response
diagnostic on B1 data (FULL_CORPUS_AUDIT §23.10) found two things:
- the scheduler's legal knowledge predicts actor-action changes at about chance;
- a receiver's OWN local MP2 score gap predicts them. The change rate is 0.30 in the lowest gap
  quintile and 0.10 in the highest.

**Does a small, locally computable, charged bid let the scheduler choose repairs worth their
bytes?**

## 2. Information and byte contract

- **Bid content.** Receiver i computes b_i at decision step t from its own sensor, its own
  packet cache and public protocol constants only, before any transmission of step t. Two
  consequences:
  - no other agent's fresh payload enters;
  - no counterfactual joint-action table, rollout value or label enters.
- **Encoders, fixed in code** (`scripts/MARL_hetero_mitigation_dev.py`, learners `bid_*`).
  - `bid_prefgap`: the preferred MP2 phase under the receiver's current cache (3 bits), plus
    min(31, round(2·score gap)) (5 bits). 1 B per receiver.
  - `bid_flag`: 1 bit, "local score gap ≤ 1.0".
  - `bid_queue`: min(255, round(own total waiting)). 1 B per receiver. This is the simple
    same-byte comparator.
  - Encoders are not trained.
- **Timing.**
  - Bids do not depend on K.
  - They are sent after the capacity reveal, on one uplink round with no request/reply, and
    before the scheduler finalises the patch.
  - Bids do not change what any actor receives. The held-phase values of the stored profiles are
    therefore unchanged, and offline evaluation is exact for this value.
- **Bytes.**
  - Bid bytes = 9 × payload + 1 B header: 10 B for `prefgap` and `queue`; 3 B for `flag`
    (9 bits → 2 B, plus 1 B header).
  - They are charged inside the SAME total cap. A method with total cap +C may spend only
    +(C − bid bytes) on patches.
  - The oracle reference for a bid method uses the same reduced patch cap.
- **Comparators at each total cap C ∈ {+28, +56, +84, none}:**
  - the no-bid legal controls `ctrl_public` and `ctrl_history`, retrained in the same trainer;
  - `bid_queue`;
  - the direct (unrestricted) policy with the same bid access, which shares the critic and is
    labelled as such;
  - `ref_joint` (PRIVILEGED), reported only as a reference.

## 3. Development (already running when this was written)

`research/marl_budget/mitigation_dev_*`:
- fit on the B1 train pool 301–364;
- epoch and τ selected on 401–408;
- development report on 501–508. That panel was OPENED by B1 and is therefore not confirmatory.

## 4. Confirmation panel

- **Fresh traffic seeds 601–616** (never used), headways 8 and 16: 32 episodes, 6 snapshots each,
  live K plus 3 capacity vectors.
  - Labels: `scripts/MARL_hetero_b2_collect.py`, with the same environment, actor and candidate
    family (imports the B1 collector).
  - Replays: `MARL_hetero_mirror_replay.py` and `MARL_hetero_response_replay.py`, both unchanged.
- **Evaluation:** `scripts/MARL_hetero_b2_confirm.py` loads the FROZEN development models
  (`model_*_s{0,1,2}.pt`) and their frozen τ. No refitting and no re-selection. The confirmation
  panel is read once.

## 5. Design freeze rule (mechanical, applied to the development report)

- **Candidates:** bid ∈ {prefgap, flag, queue} × policy ∈ {repair_R1, direct} × total cap
  C ∈ {+28, +56, +84}.
- **Choose (bid\*, policy\*, C\*)** maximising the seed-averaged development gain difference
  against the better no-bid legal control (ctrl_public or ctrl_history, by development gain) at
  the same C and the same policy.
- **Stop rule.** If no candidate has a positive difference, B2 STOPS: no confirmation data are
  collected, and the result is reported as negative.
- The chosen tuple, the control and the development numbers are appended below as "§5 FROZEN
  DESIGN" before `MARL_hetero_b2_collect.py` is run for real.

## 6. Endpoint and PASS rule (confirmation panel)

- **Endpoint.** Δ = gain(bid\*) − gain(control\*) at (policy\*, C\*), per group. Each method is
  averaged over its 3 initialisation seeds.
- **Uncertainty.** A cluster bootstrap over the 32 confirmation episodes, 10,000 resamples.
- **PASS iff all hold:**
  1. the 95% lower bound of Δ is > 0;
  2. the 95% lower bound of bid\*'s own gain is > 0;
  3. each of bid\*'s 3 seeds has a gain > 0;
  4. if bid\* ≠ queue, the mean of gain(bid\*) − gain(bid_queue) is > 0 at (policy\*, C\*).
- **Always reported:**
  - every learner at every cap;
  - oracle at the reduced cap;
  - edit rate;
  - harm per edit;
  - executed-action change, per group AND per edit;
  - total bytes including bids;
  - the direct policy with the same bid access.
- **A PASS supports only** "a charged receiver-local bid improves repair selection on frozen MP2
  / held-phase H=3 / 3×3". It is not a learned closed-loop MARL result.

## 7. Artifacts

- **Development jobs** store model state and normalisation, τ per (cap, policy), chosen indices
  and per-group gains.
- **Confirmation** stores the frozen-model reference, anchored predictions, chosen indices, τ and
  per-group gains.
- Manifests store source hashes. Confirmation labels are hashed before evaluation.

## Amendment 1 (27/09/2026 ~22:55, before the design freeze and before any confirmation label exists)

**Reason.** During development, three further receiver-local bids were designed on DEVELOPMENT
data only (the opened B1 panels 301–364, 401–408 and 501–508):
- request bids (`MARL_hetero_bid_replay.py`, `MARL_hetero_bid_request_dev.py`);
- top-2 bids with the scheduler-side refresh score (`MARL_hetero_bid_replay_v2.py`,
  `MARL_hetero_bid_top2_dev.py`);
- a legal joint-action emulation built on the top-2 bid (`MARL_hetero_top2_joint_dev.py`).

**Byte contract.** Each is 1 B per receiver plus a 1 B header, 10 B in all, charged inside the SAME
total cap exactly as in §2. The information contract is unchanged:
- bids come from the receiver's own sensor and own cache before transmission;
- the scheduler-side quantities come from the public topology, the known MP2 code and the legal
  receiver mirror;
- privileged counterfactual actions are used only as TRAINING labels (stage A of
  `mlp_top2_joint`), never as inference inputs.

**Candidate set for §5.** The candidate set becomes the six LEARNED bids:
- bid_prefgap, bid_flag, bid_queue;
- mlp_bid_request, mlp_top2, mlp_top2_joint.

Each is crossed with policy ∈ {repair_R1, direct} and C ∈ {+28, +56, +84}.

- **Rule-based variants** (rule_request*, rule_top2*) are reported but NOT candidates. The
  confirmation code evaluates frozen models and thresholds, and the rules were weaker on
  development data.
- **Everything else in §5 and §6 is unchanged:**
  - the control is the better no-bid legal control by development gain at the same (C, policy);
  - the stop rule applies if no positive difference exists;
  - the PASS criteria stay the same, with c4 against bid_queue.
- **Confirmation code:** `scripts/MARL_hetero_b2_confirm_v2.py` via
  `scripts/RUN_marl_b2_confirm_v2.sh`. It adds the request and top-2 bid replays and loads the
  frozen stage-A model. v1 is unchanged.

## §5 FROZEN DESIGN (2026-09-27 22:49:52; applied mechanically by scripts/MARL_hetero_b2_freeze.py)

Chosen: **bid = mlp_top2_joint, policy = direct, total cap C = +84, control = ctrl_history**.
Development difference +1.584 (+3.194 vs +1.609), seed-averaged, 501-508.
Files: `research/marl_budget/b2_freeze_20260927/freeze.json`, `research/marl_budget/b2_freeze_20260927/dev_map.json`, full ranking `research/marl_budget/b2_freeze_20260927/freeze_table.json`. Top 8:

| bid | C | policy | control | bid gain | control gain | diff |
|---|---|---|---|---|---|---|
| mlp_top2_joint | +84 | direct | ctrl_history | +3.194 | +1.609 | +1.584 |
| mlp_top2_joint | +56 | direct | ctrl_public | +2.498 | +1.305 | +1.194 |
| bid_prefgap | +84 | direct | ctrl_history | +2.757 | +1.609 | +1.148 |
| bid_prefgap | +84 | repair_R1 | ctrl_public | +1.911 | +0.828 | +1.082 |
| bid_prefgap | +56 | direct | ctrl_public | +2.257 | +1.305 | +0.952 |
| mlp_top2 | +84 | repair_R1 | ctrl_public | +1.763 | +0.828 | +0.935 |
| bid_prefgap | +56 | repair_R1 | ctrl_public | +1.864 | +0.937 | +0.927 |
| mlp_top2 | +56 | direct | ctrl_public | +1.951 | +1.305 | +0.647 |

No confirmation label existed when this section was written.
