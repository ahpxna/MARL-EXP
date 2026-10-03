# Pre-specified test B: a channel that SWITCHES regime within the episode — does the regime-identifying mixture receiver keep up?

Written 02/10/2026 15:1x EDT (`date` 15:14:00 before writing), BEFORE any run on the panel below (smokes on development episode
901 only: schedules k1 and iid reproduce the age-clip evaluator at K = 1 and iid exactly — parity — and alt4 runs).  User
15:1x: "làm A B trước đi".  Source: H-RID (L-278) — relayMIX's age response is regime-conditional, i.e. it identifies the
regime from its view; specialists (relayCK1, relay6Cage) are each compatible with one regime only.

## Design (scripts/MARL_e3_switch_eval.py)
Schedules of the capacity trace (26 decision steps): k1, iid (the pure regimes, references), k1_iid (K1 for steps 0–12, then
iid), iid_k1 (the reverse), alt4 (K1 / iid alternating every 4 steps).  Receivers relayMIX_st, relayCK1_st, relay6Cage_st,
seeds 0–4; Z = distill_none.  Panel 4401–4464 × 8/16 (unused; manifests grep-checked 15:1x), used once.  Endpoint, pairing,
two-level bootstrap as PROTOCOL_E3_TRAIN_MATCH_K1.

## Predictions (fixed now; means over seeds 0–4)
- SW1: on each switching schedule (k1_iid, iid_k1, alt4) relayMIX's gain vs Z ≥ both specialists' gains.
- SW2 (identification cost small): relayMIX's gain on each switching schedule ≥ the mean of its own k1 and iid gains − 0.5.
- SW3 (reported): each specialist's switching gain lies between its two pure-regime gains.
Reading fixed now: SW1 + SW2 → regime identification works online (the mixture receiver tracks a channel that changes within
an episode); SW2 failing → identification lags at the switch (a cost the static E4 test could not see).
