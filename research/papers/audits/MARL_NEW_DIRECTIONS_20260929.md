# New directions for the MARL/E3 track from the old papers' EXPERIMENTS, and their checks (29/09/2026, started 22:4x EDT)

This file keeps the directions from being lost (user, 22:4x: "ghi lại cái này chưa? kẻo quên?").  Every number is
development evidence unless marked otherwise.  The ledger entries are L-123 … L-129 in
`research/papers/audits/MARL_SELF_AUDIT_LEDGER_20260928.md`.  The old artifacts read are listed in L-123.

## The three directions (proposed 22:1x, L-123)

### 1. Receiver-side handling of incomplete sets
- Old-paper lesson: MASTER (a missing query type gives value 0, silently); SUPPORT (pairwise ≠ whole fibre).
- **Status: CHECKED.**  D3/D3b (L-124 … L-126); the new panel (L-127).
- The full-information set actor collapses under the capacity process because of STALE cached blocks it never saw in
  training.
- FO (full-information training, fresh-only pooling at the receiver) under the prefix:
  - −3.3 % vs set_none_s0 on the development panel;
  - **−3.0 % [−4.1, −1.8] on the new panel 2001–2064 (seed 0, pre-registered: PASS)**.
- It needs all three components:
  - set aggregation over present senders;
  - train and deploy inputs that agree;
  - training that sees the information.
- Pending:
  - seed 1 (set_full_s1 training, then vs set_none_s1 on the new panel);
  - set_fresh_s0 (prefix training with fresh-only inputs): is full-bandwidth training needed?
- **Caveat found 22:4x (L-129):** a 0-byte student distilled from the same teacher equals FO.  FO − student is +0.1 %
  [−0.9, +1.0] on the development panel.  So FO's gain is, so far, training-time communication, not deployment messages.
  Addendum 1 of the protocol (sha256 ae84a9b4…) adds this comparator on the new panel.
- **On the new panel (22:5x): FO − student is +1.3 % [+0.3, +2.2], so the 0-byte student is BETTER.**  The student is
  −4.2 % vs set_none_s0; only full delivery beats it (−2.7 %).

### 2. Compress the payload to a decision summary, so that all senders fit a BYTE budget
- Old-paper lessons: UNIFIED (deciding costs ≪ identifying, ratio 1/h²); QUERY (the measurement sets the order); N6
  (contrasts are free under an unknown offset); N5 (resolution: a tolerance is met at every noise level below a critical
  radius).
- This is a NEW protocol variant, bytes-limited instead of packet-limited.  It is not PROTOCOL_HETERO_v0 and must be
  declared before any claim.
- **Status: CHECKED (D5, L-130); seed 0 PASSED on the pre-registered panel 2101–2164 (L-131).**
  - Protocol: `research/marl_budget/PROTOCOL_E3_BYTEBUDGET_20260929.md`, sha256 a5639388….
  - Development panel: compressed full delivery 2–5 B/packet is −6.0 … −6.6 % vs set_none_s0; raw is −5.8 %.
  - Byte-budget variant (capacity 25·K_i bytes, 3 B packets, fresh-only): **−2.9 % [−3.9, −2.0] vs the 0-byte distilled
    student at 27 B/step** (prefix: 188.7 B/step).  Compression vs raw full: −0.2 % (free).
  - Pending: seed 1 (set_full_s1, distill_none_s1); a TRAINED compressed-payload actor.
  - Codebook: `scripts/MARL_e3_payload_codebook.py` → `research/marl_budget/e3_payload_codebook_20260929.json`, fitted on
    TRAIN traffic (301–304).  2 / 3 / 4 / 5 B per packet instead of 25 B.
  - Adapter: `models/marl_comm_actor_quant.py`.  Eval: `scripts/MARL_e3_delivery_eval_v7.py --quant L --byte-capacity bpp`.
  - Parity checks: `--quant 0` reproduces v6; bpp 3 + L 4 + prefix equals full + L 4.
- The raw payload has low entropy on training traffic:
  - phase_elapsed is essentially {0, 10, 20} s;
  - median waiting per slot is 0.

### 3. Communicate only when local information is not enough (QUERY's signal condition, UNIFIED's no-measurement phase)
- **Status: CHECKED, offline (L-128).**  `scripts/MARL_e3_msg_response_rate.py` →
  `research/marl_budget/e3_msg_response_rate_20260929.json`: set_full_s0 under full delivery, 64 episodes, 14,976
  receiver-steps.
- Messages change the actor's action in **34.5 %** of receiver-steps (h8 30 %, h16 39 %).
  - This is NOT sparse like QUERY's RWARE panel (5–28 %).
- The receiver's own no-message margin predicts which steps change: AUC 0.73.  Own waiting 0.63; headway 0.55.
- Request gate "ask iff margin < τ":
  - 50 % of receiver-steps capture 72 % of the changes;
  - 70 % capture 91 %;
  - but a step with NO request at all is rare (0.3 % at 50 %);
  - a neighbour-gated sender still transmits 81 % of the time.
- **Reading: little byte saving on a broadcast stream.**  E3's decision signal is dense.  QUERY's sparsity does not
  transfer.  Direction 3 is deprioritised.

## The components the current pipeline USES, against the old experiments (user, 22:4x)

| component in E3 | old experiment and its lesson | check | result |
|---|---|---|---|
| stream order = plug-in ranking by cached waiting | Paper A deployable: the plug-in surrogate rule censored 942/2400 runs (39 %), geometry and uniform rules 0 | D4a: FO under random / nbr / rxold / rxq orders | all within 0.3–0.6 % of the prefix (n.s.). Starvation does not bite under FO |
| one broadcast order for all capacities (nested prefix) | STRUCTURAL: one ranking reaches 1/(2r) on staircases; a menu can be needed | D4a (receiver menus nbr / rxq) | no gain over the nested prefix |
| cached stale blocks, age inputs | FUNCTIONAL certificate lifetime; ADAPTIVE bounded age | D3 (drop stale), D4a rxold | dropping stale is the lever; age-first order adds nothing |
| flat MLP over fixed slots | SUPPORT (whole fibre vs pairs); N6.3 (two query types suffice) | D3b, rc_noise | the set actor is needed. H1 refuted: noise in the message slots does NOT harm the flat actor (+1.6 % vs set_none, −1.1 % vs flat none; the rule needed ≥ +4 %) |
| 25 B raw-state payload | UNIFIED decide ≪ identify; QUERY; N5 resolution | D5 | running |
| checkpoint = min SELECT over 100 noisy evaluations | A7 stopping chain (certified in the correct direction); L-111 | D4b: last checkpoints | FO last: −3.4 % (prefix), −4.0 % (cap 4). Not a selection artifact |
| training signal (MAPPO from scratch) | Paper A (repair by β-mixing); asymmetric / teacher–student | distill_none_s0 (L-122) | **0-byte student −3.2 % vs set_none_s0, equal to FO** |
| sender-side selectors (critics, τ-rule) | N3: adaptivity gain < 2; two batches suffice | none (L-69 … L-89 already negative) | stop |
| reference controller MP2 | MASTER reference held-out calibration | L-114 … L-116 | maxq is the honest heuristic |

## Consolidated reading at 22:5x (development)
- Information to a trained set actor is worth about 74 vehicle-steps per episode at full delivery.
  - Under the capacity process, the value that can be kept at deployment (FO) equals what a 0-byte student distilled from
    the full-information teacher already has.
- The replicated positive claim is "communication in TRAINING": a full-information teacher, distilled into a 0-byte
  policy.
  - It is −3.2 % vs set_none_s0 on the development panel and −4.2 % on the new panel.
  - It beats FO by 1.3 % on the new panel.
  - It holds against set_none_s1: −46 vehicle-steps at both loads.
  - It rests on one teacher seed and one student seed; a seed-1 student is needed.
- The deployment value of messages beyond that exists only near-complete sets: capacities 5–7 give −6.0 %; full gives
  −6.7 % on the new panel.  Hence direction 2 (fit all senders in the byte budget) is the one road to deployment value.
- **22:5x: direction 2 delivers that road for seed 0.**  3 B decision summaries let every receiver decode all 8 senders
  within its byte budget.  This beats the 0-byte student by 2.9 % on an unused panel, at 14 % of the prefix's bytes.  The
  candidate method is:
  - train with full information;
  - send compressed decision summaries;
  - pool only fresh packets at the receiver.
- The method needs seed 1 before it is read as more than a single-seed development result.

## 23:4x update (L-137)
- **A distilled student WITH fresh-only messages** (`distill_fo_prefix_s0`) beats the 0-byte student INSIDE the packet
  protocol HETERO_v0.
  - Development panel: −2.1 % [−3.0, −1.1] under the prefix; −2.0 % under cap 4 (100 B/step).
  - Pre-registered on panel 2201–2264: `research/marl_budget/PROTOCOL_E3_FOSTUDENT_20260929.md` (sha256 8a793581…).
    Seed 1 is distilling.
- **Complete presence fixes even the flat actor.**  Under the byte-budget variant the flat full actors equal their raw
  full delivery.
- **Byte-budget frontier** vs the 0-byte student: 3 B slots −3.5 %, 6 B −2.9 %, 12 B −1.7 %, 25 B −0.2 %.  The number of
  senders decoded carries the value.
- maxq on the new panels: every learned 0-byte or communicating policy is 18–23 % better.

## 00:2x (30/09) status of the pre-registered protocols (L-139 … L-144)
| protocol | seed 0 | seed 1 | verdict |
|---|---|---|---|
| FRESHONLY: FO vs set_none | −3.0 % PASS | −5.2 % PASS | supported vs set_none |
| FRESHONLY addendum 1: FO vs the 0-byte student | student better (+1.3 %) | student better (+2.1 %) | FO's gain is training-time |
| BYTEBUDGET: 3 B, 27 B/step vs the 0-byte student | −2.9 % PASS | −3.7 % PASS | **supported (both seeds)** |
| FOSTUDENT: fresh-only student vs the 0-byte student | −0.8 % FAIL | −4.0 % PASS | not supported (seed-dependent) |
| SETFRESH: set_fresh vs the 0-byte student (HETERO_v0 unchanged) | −2.0 % PASS | +7.2 % FAIL | not supported (seed-dependent) |
| TRAINEDQ4: trained 3 B actor, byte budget, vs the 0-byte student (panel 2401–2464) | −5.3 % PASS | −4.2 % PASS | **supported (both seeds)** |

Also:
- The TRAINED compressed actor (set_fullq4_s0) gives −4.6 % vs the student on the development panel.  Not yet
  pre-registered; seed 1 is training.
- The 0-byte student beats set_none by −4.0 % (seed 0) and −5.2 … −7.1 % (seed 1) on every panel.

**00:3x verdict (L-146).**
- Inside the packet protocol HETERO_v0, no design passes both seeds against the 0-byte distilled student.
- Only the byte-budget variant with 3 B decision summaries does (−2.9 / −3.7 %).
- Training-seed variance is large: set_fresh differs by about 7 % between seeds.  More training seeds are needed for any
  claim.

**02:5x (L-149 … L-151).**
- CONTROLS (seed 0): a no-communication teacher gives a student +0.2 % vs set_none; extra PPO compute +2.0 %; a
  partial-information teacher −2.3 %; a full teacher −3.2 %.  The 0-byte student's gain is the teacher's INFORMATION
  (seed-1 controls running).
- Extra set_fresh seeds are typical at −2 % vs set_none and do not beat the student.
- The byte-limited channel with 3 B summaries is supported on 2 seeds × 3 panels (eval-only compression) and 2 seeds × 1
  panel (trained compression).

## Next checks, smallest first
1. D5 result (running).  If compressed full delivery keeps most of −5.8 %, pre-register the bytes-limited variant with a
   trained compressed-payload actor (not eval-only).
2. Addendum-1 comparator on the new panel (running): FO vs the distilled student.
3. Seed 1 of FO (set_full_s1, training) and a seed-1 student distilled from it.
4. set_fresh_s0 (training): FO without full-bandwidth training.
5. A distilled student WITH fresh-only messages (student delivery prefix, freshonly adapter).  It combines training-time
   and deployment-time communication.

## Related work checked (30/09 09:1x) and where our results sit
- **Distillation of a privileged or centralised teacher into communication-free students** is established: CTDS (arXiv
  2203.08412), PTDE (IJCAI 2024), CADP, communication-enhanced tutoring (arXiv 2508.13661), KD-MARL (arXiv 2604.06691).
  - Ours is not a new distillation method.
  - It is a BASELINE and a MEASUREMENT: in budgeted communication, a distilled 0-byte student is the bar for any claim
    about deployment messages.
  - The controls (L-149, L-152, L-153) show its gain is the teacher's information: none ≈ 0 < prefix < full, on 2 seeds.
- **Chauhan & Bera, "Emergence, Not Bandwidth" (arXiv 2609.34373, 28/09/2026)**:
  - With 2-bit budgets in MuJoCo teams, learned communication is often indistinguishable from silence.
  - Engineered senders beat learned ones, and learned protocols are unintelligible across seeds.
  - Their baselines are silence and engineered senders, NOT a distilled student.
  - Our 3 B codebook is an engineered (fitted) sender with a learned receiver, which is consistent with their finding.
  - Our additions: the distilled-student bar; the packet-capacity mechanism (sparse presence + stale cache); and a positive
    result under a byte-limited channel.
- **Bandwidth-limited or compressed MARL messaging**:
  - IB + VQ (arXiv 2602.02035);
  - bandwidth-constrained variational message encoding (arXiv 2512.11179);
  - event-triggered ETCNet (arXiv 2010.04978);
  - task-effective compression over bit-budgeted channels (arXiv 2301.01628);
  - communication-constrained priors (arXiv 2512.03528).
  - These compress messages.  The abstracts checked do not report a distilled no-communication student as a comparator.
- **Traffic control**: CoLight (graph attention over neighbours) and MPLight.  Our attention actor equals mean pooling
  (L-133).
- Lowe et al. (AAMAS 2019): compare against agents trained from scratch without communication.  We do that AND add the
  distilled student.

## Proof experiments planned 09:1x (to pre-register before running)
- P1: more training seeds (running, L-154).
- P2: OUT-OF-DISTRIBUTION demand (headways 6, 12, 24, never trained), pre-registered.
- P3: codebook robustness (refit on other TRAIN seeds with another behaviour policy), a diagnostic.
- P4: packet-loss robustness of the fresh-only set receiver, a diagnostic.

## 10:1x (30/09) five-seed synthesis (L-160), development panel, two-level bootstrap
| comparison | per seed | mean [95 % CI] | seeds below 0 |
|---|---|---|---|
| 0-byte student vs set_none | −3.2 −6.3 −3.0 −2.7 −2.2 | −3.5 % [−4.9, −2.2] | 5/5 |
| C1: no-comm-teacher student vs set_none | +0.2 −0.2 +0.2 | +0.1 % [−0.5, +0.6] | 1/3 (null) |
| **BYTEBUDGET (raw teacher, 3 B at deployment) vs the student** | −3.5 −4.5 −4.5 −2.5 −3.0 | **−3.6 % [−4.5, −2.7]** | **5/5** |
| TRAINEDQ4 (trained on 3 B) vs the student | −4.6 −4.3 +5.1 | −1.3 % [−4.9, +4.7] | 2/3 (fragile) |
| set_fresh (HETERO_v0) vs the student | −2.7 +1.0 +1.5 | −0.1 % [−2.2, +1.8] | 1/3 |

**The recommended recipe is BYTEBUDGET, not TRAINEDQ4:**
- train with full information on raw payloads;
- deploy 3 B decision summaries under a byte-limited channel;
- use a fresh-only set receiver.

It is robust:
- on 5/5 training seeds;
- on 3 pre-registered panels;
- out of distribution;
- with another codebook;
- up to 25 % packet loss.
