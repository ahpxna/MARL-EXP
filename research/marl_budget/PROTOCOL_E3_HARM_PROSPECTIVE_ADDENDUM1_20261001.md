# Addendum 1 to PROTOCOL_E3_HARM_PROSPECTIVE_20261001 — extra COMPARATORS only (H1–H3 unchanged)

Written 01/10/2026 11:51:58 EDT (`date`), while the target lanes were still running (37 of 40 arm logs present) and BEFORE
any target result was read; the waiter's report output has not been opened.  Trigger: the third external audit (user,
11:4x) and my own check of the definitions in scripts/MARL_e3_protocol_demand_report.py.

## Identity found while verifying the audit
With need = ¬(teacher-on-EMPTY-view acceptable) and harm_S = P(¬need ∧ ¬protoS),
  net_S = P(need ∧ protoS) − P(¬need ∧ ¬protoS) = P(protoS) − P(¬need) = acc_S − acc_E,
where acc_S = P(relay student's executed action ∈ A_0.25) and acc_E = 1 − N_dev = P(teacher's argmax on the local-only view ∈ A_0.25),
both on the relay student's own closed-loop states of the development panel.  So net_S is an ACCURACY DIFFERENCE, not a
separate repair/corruption mechanism; and its baseline is the teacher on the empty view, not the zero-byte student Z.

## Comparators added (reported next to H1–H3 for every K ∈ {1, 2, 3}; no pass/fail rule attached)
- C1 acc_S(K) alone; C2 −harm_S(K) alone; C3 acc_E(K) alone (all from e3_protocol_demand_report_20261001.json flags).
- C4 the DEVELOPMENT-panel closed-loop gain: relay6Cage_st_s<s> const K queue sums already in
  e3_protocol_demand_20261001/s<s>_K<K>/rows.json (seed901–904 × 8/16) against distill_none_s<s> on the same 8 episodes
  (to be produced with scripts/MARL_e3_delivery_eval_v6.py, the evaluator used for Z on every panel).  C4 is the
  natural competitor of any measure that, like net_S, needs the trained relay student run closed loop.
- Interpretation fixed now: if C4 or C1 matches or beats net_S, the "repair minus corruption" reading is not needed
  to explain the result (net_S then only proxies the deployed system's own dev-panel behaviour).
