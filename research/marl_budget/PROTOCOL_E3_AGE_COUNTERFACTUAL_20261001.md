# EXPLORATORY decision-level counterfactuals: age FEATURE vs stale CONTENT at constant K = 1

Written 01/10/2026 12:08:34 EDT (`date`), after PROTOCOL_E3_NEGFLIP_VS_Z_20261001 (X1, X3 true).  Development panel
seed901–904 × 8/16, seeds 0–9, K ∈ {1, iid}; the closed loop is unchanged (the relay student's actual actions are executed;
parity with e3_negflip_20261001 queue sums required), only RECORDED counterfactual decisions are added.

## Counterfactual views of the receiver's merged relay view (threshold A = 2 steps = the iid p95 of the maximum copy age)
- clip: every entry older than A keeps its content but its age is set to A (the age feature back inside the training range)
- drop: every entry older than A is removed (the receiver reads only copies inside the training range)
Recorded: whether the relay student's argmax on each view is in A_0.25 (teacher full view); zok as before.

## Expectations stated now (K = 1; iid is the control, where clip and drop should change little)
- Y1 age-feature extrapolation: acc_clip − acc_S ≥ 0.02 and acc_clip ≥ acc_Z.
- Y2 stale content harmful, the rest useful: acc_drop ≥ acc_Z (and > acc_S).
- Y3 stale content misleading whatever its label: acc_clip ≤ acc_S.
- Control: at iid |acc_clip − acc_S| and |acc_drop − acc_S| ≤ 0.01.
Interpretation fixed now: Y2 without Y1 → stale copies themselves hurt; a deployable test-time rule "drop copies older
than the training range" becomes a candidate for a PROSPECTIVE closed-loop test.  Y1 → the student extrapolates badly in
the age feature.  Neither → the loss needs retraining at the target capacity to diagnose.
Probe `scripts/MARL_e3_age_cf_probe.py` (decision-level only).
