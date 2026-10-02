# EXPLORATORY mechanistic probe: Need → satisfiable under ideal delivery → satisfied by the actual relay → task gain

Written 01/10/2026 11:0x EDT, AFTER the result of PROTOCOL_E3_DEMAND_FRONTIER_20261001 was read (mean relay gain by
const K: −1.65, +1.01, +1.72, +1.99, +1.97, +2.15, +2.17 %; P1 and P2 supported).  Everything here is EXPLORATORY with
respect to that result; a prospective replication on an unused panel is required before any claim.  Trigger: the external
audit's point that G′ uses the teacher on the direct cache plus the first K stream senders, which is neither the oracle best
subset nor the information the relay actually delivers (user 11:0x: "làm chỗ nó nói đúng mà chưa làm").

## System
relay6Cage_st_s<s> closed loop under age-first, capacity const K, relay v2 merge, 3 B codebook (the protocol-1 target
system), development panel seed901–seed904 × 8 / 16 (8 episodes), seeds 0–9, K ∈ {1, 2, 3, 5, 7}.  Teacher set_full_s<s>,
acceptable set A_0.25 of its full-view logits (teacher-defined proxy).  Parity: the K = 1 … 7 rollouts must equal relay v6
evaluator rows when those exist (checked in the smoke on the same episodes).

## Per receiver-step flags
- need   = teacher argmax on the EMPTY view (local observation only) ∉ A_0.25   (the zero-byte student's information)
- best_K = some cache-base subset S of size ≤ K has an acceptable teacher argmax (exhaustive over 2^|N|)   (ideal delivery)
- protoT = the teacher's argmax on the ACTUAL relay-merged view of the receiver (fresh decoded packets + relayed copies +
  cache, encoded with the 3 B adapter the student uses) ∈ A_0.25                                          (delivered info)
- protoS = the relay student's executed action ∈ A_0.25                                                  (usability)

## Quantities per (seed, K)
N = P(need); S_best = P(need ∧ best_K); S_protoT = P(need ∧ protoT); S_protoS = P(need ∧ protoS);
harm_T = P(¬need ∧ ¬protoT) and harm_S = P(¬need ∧ ¬protoS) (the delivered view makes an acceptable local decision
unacceptable: stale or misleading copies).  Gaps: N − S_best (insufficiency even under ideal delivery), S_best − S_protoT
(delivery / order / freshness loss), S_protoT − S_protoS (usability loss).  Net satisfied demand net_X = S_protoX − harm_X.

## Exploratory expectations (stated now, not a rule)
- E1: at K = 1 the harm terms are largest, so net_S is lowest, matching the negative realised gain at K = 1.
- E2: across seeds at each K, Spearman(net_S, realised gain_s(K) of protocol 1) exceeds Spearman(S_best, same).
- E3: the delivery loss S_best − S_protoT shrinks with K faster than the demand curve, matching the fast saturation of the
  realised frontier.
If E1–E3 look right, a PROSPECTIVE protocol on an unused panel follows; if not, the mechanism is reported as unexplained.

Probe `scripts/MARL_e3_protocol_demand_probe.py`, report `scripts/MARL_e3_protocol_demand_report.py`.
