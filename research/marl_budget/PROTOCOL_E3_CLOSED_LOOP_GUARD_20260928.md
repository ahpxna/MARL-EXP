# PROTOCOL E3-GUARD — re-running the closed-loop panels after the normalisation defect (registered 28/09/2026, 23:35 EDT, before any guarded run)

**Why (ledger L-65).**
- Every E3 selector normalises its context by the train mean and std + 1e-6.
- On the train states (t ≥ 7), several binary "packet present" flags and other features are constant. A changed
  value is therefore scaled by about 10⁶.
- Offline DEV states (t ≥ 10) never trigger it (the author's audit script: DEV max |z| 19.6 and 27.7).
- CLOSED LOOP does trigger it at t = 0–3, when caches are empty: |z| = 10⁶. Selectors with a small τ then edit on
  scores computed from inputs far outside their training support (replay, scratchpad `early_step_norm*.py`).

**What is run.**
- The existing closed-loop panels are rerun with the SAME frozen checkpoints and the same arguments as the original
  run (actor, selector dir and names, direct policy, cap +84, MP2 reference, pilot panel 901–916 × headways 8/16).
- The runtime is `scripts/MARL_e3_closed_loop_v6.py`: runtime v5 plus ONE declared deployment rule, the support guard.
- The normalisers of the old checkpoints are NOT changed. The guarded policy is a DIFFERENT deployment rule, reported
  as such, not as an equivalent of the old runs.

**The support guard.**
- The selector's choice is replaced by the committed prefix at a step if either condition holds:
  - (a) t < T_MIN, the earliest labelled snapshot of the selector's training labels. T_MIN = 7 for the original
    label rounds;
  - (b) the largest |normalised input| of the critic context, or of the response / multi-class head input, exceeds
    Z_MAX = 50. The largest value on the saved DEV states is 27.7.
- Bids are still sent and charged at a guarded step, as in the protocol ("charged at every step").
- Every selector row logs, per step: t, guarded, reason, the largest |z|, and edit yes/no.

**Parity.**
- With `--guard none`, v6 must reproduce v5/v3 rows exactly. This is checked on a smoke episode before the panels.

**Reading.**
- Descriptive DEVELOPMENT evidence.
- For each actor and variant, the reporter (`MARL_e3_panel_report.py`) runs on both the guarded panel and the original
  panel, with the same statistics. It also reports:
  - guarded − unguarded (paired by episode);
  - the number of guarded steps by reason;
  - edits outside the support in the unguarded runs.
- This measures how much the defect changed closed-loop decisions and waiting. It is NOT a new method.
- A proper fix for FUTURE training is a normaliser suited to binary and constant features, shared by train and runtime,
  followed by a controlled retrain. That is a separate step, not part of this rerun.
- The old rows are kept and labelled "unguarded (out-of-support decisions at t < 7)".

## Observation from the parity smoke (23:40, before the panels; the rule above is unchanged)
- Parity: with `--guard none`, v6 reproduced every one of the 28 cl_v3_direct rows of seed 901 (queue, finished,
  bytes, edits).
- With `--guard support`, 12–25 of the 26 steps are guarded, not only the 7 steps with t < 7.
- Reason: after the first edit, |z| jumps to 4e4–1.2e5 and stays there. The edit delivers a receiver–sender pair that
  the prefix never delivers in training (a mirror slot constant 0 on train). So the guarded policy edits only until its
  first out-of-support edit.
- Consequence for reading: the guarded panels measure how much of the old closed-loop outcome came from
  out-of-support decisions. They do NOT measure the selector's ability on states it never saw. That needs a safe
  normaliser and training data from such states (a separate, later decision).
