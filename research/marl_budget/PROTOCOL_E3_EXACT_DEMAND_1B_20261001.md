# Pre-specified test 1b: exact, uncensored demand curves (empty and cache bases) as predictors of the capacity frontier

Written 01/10/2026 10:5x EDT.  It reuses the TARGET runs of PROTOCOL_E3_DEMAND_FRONTIER_20261001 (panel 2801–2864,
relay6Cage_st_s0…9 under age-first const K = 1…7 vs distill_none_s0…9), which were launched at 10:42.  At the time of
writing NO result of that target has been read: its report file holds only the 10:41 "INCOMPLETE: 80 arms missing" stub
written before the launch; only directory counts were listed.  Trigger: the external audit of 10:4x (user 10:4x) — exact
subsets instead of the size-2 cap, an empty base, a combined predictor, comparator predictors.

## New predictor probe (development panel, independent of the target)
`scripts/MARL_e3_decision_depth_probe_v4.py` = the V-D v1 probe (same system: relay6Cage_st_s<s> closed loop, age-first,
low capacity; same teacher set_full_s<s>; same acceptable set A_0.25 of the teacher's full-view logits — a labelled,
teacher-defined proxy) with, at every receiver-step:
- EXHAUSTIVE subsets of the receiver's 8 neighbours (2^8 = 256), no cap;
- two bases: CACHE (zero-fresh view keeps stale cached copies, the V-D v1 / N_s base) and EMPTY (view stripped to the local
  observation: the zero-byte student's information);
- d_min^B = least |S| with an acceptable teacher argmax on base B plus fresh S (exact 0…8); d_prefix^B = least k with the
  first k senders of the executed age-first stream (exact);
- the teacher's full-view top-2 logit margin.
Episodes seed901–seed916 × load 8 / 16 (32 episodes, 7 488 receiver-steps per seed), all ten seeds; parity with the
satrot rows required.

## Predictors (functions of the probe only)
- Q^B_prefix(k) = P[d_prefix^B > k], Q^B_min(k) = P[d_min^B > k].
- PRIMARY combined predictor (the zero-byte student holds the EMPTY information; the relay student at capacity K holds
  roughly the cache plus K fresh stream senders): G'_s(K) = Q^∅_prefix(0) − Q^C_prefix(K), and Ḡ'_s = mean over K = 1…7.
- Comparators (reported for every target statistic): N_s = Q^C_prefix(0) (the earlier predictor); Q^∅_prefix(0);
  demand areas A^∅_s = Σ_{k=0}^{7} Q^∅_prefix(k) and A^C_s; D_s (1 − distillation agreement, protocol values); the
  teacher's mean full-view margin.
- Order tax curve T^B(k) = Q^B_prefix(k) − Q^B_min(k) (reported only; it is the input of a later recourse test).

## Predictions and rules (fixed now)
- P1b: Spearman(Ḡ'_s, Ḡ_s) ≥ 0.5, with Ḡ_s = mean over K of the realised gain (protocol 1's endpoint).
- P1b-cmp: Spearman(Ḡ'_s, Ḡ_s) > Spearman(N_s, Ḡ_s) (the uncensored, two-base predictor beats the earlier one).
- P1b-shape: with g̃(K) the protocol-1 normalised mean frontier and Ĝ'(K) = mean_s G'_s(K) / max_K mean_s G'_s(K),
  MAD(Ĝ') < MAD(STEP) and MAD(Ĝ') < MAD(LINEAR) (the same nulls as protocol 1).
- Every comparator's Spearman with Ḡ_s is reported; if any comparator other than N_s exceeds Ḡ'_s, that is stated as a
  failure of P1b-cmp in spirit even when the letter holds.
- Multiplicity: protocols 1 and 1b test five rules on one target; they are reported together, none is dropped.

## Not changed after this file
Probe definition, episodes, bases, predictors, P1b, P1b-cmp, P1b-shape.  The probe and the report
`scripts/MARL_e3_exact_demand_report.py` are written before the probe runs; the report reads protocol 1's target only
through the same files and checks as protocol 1's report.
