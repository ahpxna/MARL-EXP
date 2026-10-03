# Pre-specified test: a pre-deployment PROBE of what a learned receiver uses age for (reliability vs propagation)

Written 02/10/2026 12:2x EDT (`date` 12:24:39 before writing), BEFORE the age-role testbed results (PROTOCOL_RI_AGE_ROLE,
running; results.json did not exist at writing) and BEFORE the MARL age-remap report (PROTOCOL_E3_AGE_REMAP, 66 / 90
evaluations done, nothing read).  User 12:2x: "probe thì sao".

## The probe (model + training-distribution inputs only; no deployment data)
For an input with a remote copy of age δ: d = f(input) − f_silent(input) (the message's effect on the output) and
Δ = f(input with every age label + 1 step) − f(input) (the effect of the age label, content fixed).  Reliability share
ρ = Σ ⟨Δ, d⟩² / ‖d‖² / Σ ‖Δ‖² (inputs with ‖d‖ below 1e-6 skipped): the fraction of the label effect that only scales the
message's effect (a pure trust weight gives ρ = 1; a propagation horizon moves the output in other directions, ρ < 1).
Decision rule proposed: a training-free age relabel is admissible for upgrades when ρ is high; otherwise use emulation.
* Testbed (scripts/RI_age_role_probe.py): the slow-trained predictors of PROTOCOL_RI_AGE_ROLE re-trained bit-identically
  (same code path and seeds), f_silent = the local-only predictor; inputs = the training inputs (δ ~ U{4..7}).
* MARL (scripts/MARL_e3_age_role_probe.py): relay6Cage_st_s0–4 at iid and relayCK1_st_s0–4 at const K = 1 (each on its
  TRAINING channel), development episodes 901–904 × 8/16 (no target panel), closed loop under the plain student; outputs =
  log-softmax action vectors; f_silent = the same student on its local-only view (inbox and cache removed, as
  MARL_e3_watch_relay.local_only); the +1 relabel applies to every present entry.

## Predictions (fixed now)
- PR1: in the testbed ρ falls strictly with the drift λ (0, 0.1, 0.2, 0.4; mean over seeds).
- PR2: in the testbed ρ ranks the remap harm h(λ) of PROTOCOL_RI_AGE_ROLE: Spearman(ρ, h) = −1 over the four λ.
- PR3 (MARL, the cross-domain prediction): if the MARL receivers' mean ρ is ≥ the testbed's ρ at λ = 0.1, the age remap is
  predicted to repair the upgrade (RM1 of PROTOCOL_E3_AGE_REMAP supported); if it is ≤ the testbed's ρ at λ = 0.4, RM1 is
  predicted to fail.  (Scored when both reports exist; in between: no prediction.)
Exploratory: n = 5 per cell; no significance rule.
