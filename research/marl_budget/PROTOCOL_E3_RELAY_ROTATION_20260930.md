# Relay packets with a rotating stream head, inside PROTOCOL_HETERO_v0 (DEVELOPMENT-CONFIRM protocol, 30/09/2026, written 15:0x EDT)

This is written BEFORE any run on the panel below.  Development evidence: ledger L-162, L-163, L-165, L-168, L-169, L-172 and
the parallel session's saturated-age re-measure (`research/marl_budget/e3_satrot_eval_20260930/`).

## Where this comes from (development panel 901–964, already seen)
- Channel: PROTOCOL_HETERO_v0 unchanged.
  - One broadcast stream of 25 B packets.
  - Receiver i decodes the first K_i packets of the committed order.
  - Accounting is that of the prefix rule.
- Packet content: RELAY (`models/marl_relay_v2.py`).
  - Positional slots: the sender's own 17-bit summary, plus 8 × (17-bit summary + 4-bit age).  That is 185 bits ≤ 200 bits
    (the L-165 layout).
  - Ages are saturated at 14 decision steps; code 15 means "absent".
  - Summaries use the v1 TRAIN codebook, L = 4 (`research/marl_budget/e3_payload_codebook_20260929.json`).
  - The receiver merges, keeping the freshest copy per agent.
- Stream order: AGEFIRST, oldest last-broadcast first (scheduler information only).
  - It is applied through `models/marl_delivery_music.py`, which keeps the cap<c> rule under every order (L-168: the
    original `deliver_agefirst` ignored it).
  - The evaluator checks at every step that the scheduler-side AgeMirror equals the merged views.
- Students: relay_st_s s, s ∈ {0, 1}.
  - DAgger students of the full-information teacher set_full_s s, trained under the PREFIX order with exact ages (distill v4).
  - The order and the age layout change at EVALUATION only.
- Development results vs the same-seed 0-byte distilled student (L-169; saturated ages give 768/768 identical rows under
  agefirst):

| condition | s0 | s1 |
|---|---|---|
| iid prefix decoding | −3.1 % | −3.2 % |
| cap4 | −2.3 % | −4.1 % |
| low capacity | −2.8 % | −3.0 % |

- The same students under the default prefix order: cap4 +0.9 % (s0) / −1.6 % (s1); low +0.4 % / −1.4 %.

## Hypothesis
Inside the unchanged packet channel, relay packets with a rotating stream head beat the best 0-byte policy (the distilled
student of the same teacher) under every tested receiver-capacity condition, including the low-capacity ones where the default
order starves most senders.

## Arms, conditions, comparators
- **Arm**: relay_st_s s, s ∈ {0, 1}.
  - Evaluator: `scripts/MARL_e3_delivery_eval_relay_satrot.py --relay age --quant 4 --order agefirst`.
  - It runs the full per-step access audit and the AgeMirror check.
- **Conditions** (all on the same traffic episodes):
  - C1, iid: `--capacity iid --deliveries prefix`, K_i ~ U{1..7}, about 189 B/step;
  - C2, cap4: `--capacity iid --deliveries cap4`, the stream capped at 4 packets, 100 B/step;
  - C3, low: `--capacity low --deliveries prefix`, K_i ~ U{1..3}, about 94 B/step.
- **PRIMARY comparator**: distill_none_s s (0 B).
  - Evaluated with `scripts/MARL_e3_delivery_eval_v6.py --deliveries none`.
  - It has no messages, so one set of rows serves all three conditions.
- **Secondary**, reported as measured and never used to rescue the primary:
  - the same students under the PREFIX order in C1–C3: the rotation effect, paired;
  - BYTEBUDGET: set_full_s s with eval-only 3 B, `--byte-capacity 3 --adapter-override freshonly`, 27 B/step.  It is a
    different channel model and serves as a reference;
  - set_none_s s;
  - maxq, the heuristic;
  - bytes per episode of every arm.

## Panel
- **Traffic seeds 2601–2664 × headways 8 / 16**, 128 episodes per condition.
- At 14:5x–15:0x it was checked unused for any E3 episode: no manifest in `research/` or `legacy/` lists these seeds, and no
  rows, launcher or protocol does.
- It is used once.

## Pre-stated criterion
- **PRIMARY**, per seed s and condition c:
  - statistic: the ratio of summed waiting, arm / distill_none_s s, minus 1;
  - uncertainty: a bootstrap over traffic seeds, with both headways of a seed resampled together, 4000 resamples, seed 0;
  - the upper 95 % bound must be < 0.
- **Supported only if all 6 cells pass** (2 seeds × 3 conditions).
  - Any failed cell means NOT SUPPORTED.
  - A cell whose evaluation fails permanently makes the verdict INCOMPLETE.  It is not replaced by another panel.
- Stalls and watchdog retries are reported.  CityFlow is deterministic per episode, so a retry reproduces the same rows.

## Not claimed
- This is not the reserved test (1301–1316 stays closed).
- Two training seeds only.  L-170 shows that the teacher's quality sets the size of such gains; seeds 5–9 have weaker teachers.
- The rotation is an evaluation-time change for students trained under the prefix order.  Students trained under the
  rotation (relay6Cage, parallel session) are not part of this protocol.
- The "bass" order is not tested: it equals agefirst on the development panel (L-169).
- Guardrails (finished trips, throughput) are not recorded by these evaluators.
- The relay mechanism itself has prior art (Gama et al. 2012.14906; NeurComm, ICLR 2020; L-166).  This protocol tests the
  measured claim, not novelty.
