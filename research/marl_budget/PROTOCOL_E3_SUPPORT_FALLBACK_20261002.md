# PROTOCOL E3-FB — a support monitor with fallback to the compiled-silent student, against a freshness monitor
# (written 02/10/2026 22:2x EDT, before any fallback run; user 22:0x "ok làm số 3 và 4 đi")

## Question
The E3 receivers fail when the deployment channel leaves their TRAINING SUPPORT (L-250 upgrade hazard, L-270 K = 1 reversal,
L-286 train-match, L-287 test C).  A deployable repair that needs no retraining: every intersection carries its relay receiver
AND the zero-byte student Z distilled from the same teacher; a monitor reading only the receiver's own merged view decides, per
agent and per decision, which of the two acts.  Does a SUPPORT monitor (is this view configuration one the receiver saw in its
own training logs?) repair the hazard cells while keeping the gain elsewhere, and does it beat the AoI reflex "ignore messages
when they are too old" (a FRESHNESS monitor), which by construction cannot see an upgrade to a fresher channel?

## Novelty check (22:1x, standard web search; verdict before building)
Monitor + fallback is standard: Simplex / runtime assurance (Neural Simplex arXiv 1908.00528; arXiv 2010.10618), OOD detection
for safe RL (AAAI 2023 student abstract, OOD dynamics), box monitors on activations (Henzinger et al. 2020), MARL OOD signalling
(Unexpected Encoding Scheme, arXiv 2501.01140).  AoI work discards or re-samples on age thresholds.  Not found: a fallback whose
trigger is the CHANNEL configuration relative to the receiver's training support, whose fallback is the same-teacher compiled-silent
student, tested against an age-threshold trigger on upgrade (fresher-channel) hazards.  Claimed contribution (narrow): the measured
statement "freshness gating is blind to the upgrade hazard; support gating is not", on two networks.  The monitor itself is not new.

## What this is NOT (user 22:1x)
CityFlow simulation; receivers, Z and teachers are our own trained networks; synthetic grid demand.  No real controller logs, no
J2735 traces, no independently developed vehicle or controller stack, no real cross-version data.  Any transfer claim beyond
"two simulated networks with our own learned components" is out of scope.

## Setup
* Networks and components (unchanged checkpoints): 3×3 research/marl_budget/e3_delivery_actors_20260929 — receivers relay6Cage_st
  (trained iid), relayCK1_st (const1), relayMIX_st (iid, const1, const2, const3), relayMIX2_st (iid, const1), Z = distill_none,
  seeds 0–4; 4×4 research/marl_budget/e3_grid4x4_20260930/actors — relayCage_st (iid), relayCK1_st (const1), Z = distill_none,
  seeds 0–9, through scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 (relayMIX_st 4×4 added as a
  secondary after test D finishes; not part of the predictions).
* Deployment channels K ∈ {1, 2, 3, iid}, age-first order, prefix delivery, relay v2 merge, 3 B codebook: the code path of
  scripts/MARL_e3_ageclip_eval.py with --A −1.
* Panels: 3×3 4801–4864 × headways {8, 16}; 4×4 4901–4964 × {8, 16} (both checked unused by scripts/UTIL_panel_unused.py
  before the run; if 4901 is used, the next unused block of 64 is taken and recorded).
* Calibration (the receiver's own TRAINING logs; no panel episode): the receiver in closed loop under its TRAINING channel on its
  training episodes 301–332 × {8, 16} (scripts/MARL_e3_actor_train.TRAIN); a mixture receiver runs its regimes in rotation
  (episode index mod number of regimes).
* View statistics, from the merged view the receiver reads (ages in decision steps, capped at 14 by the relay; an agent with no
  entry counts as missing).  Over the m − 1 other agents (8 on 3×3, 15 on 4×4: the receiver's input has one block per other
  agent; corrected 22:26 after the 4×4 smoke showed 9 entries — the slot restriction limits what a sender RELAYS, not what a
  receiver holds — before any panel run):
  - support key = (time bin of t ∈ {0–4, 5–12, 13–25}; counts of the m − 1 agents with age 0, 1, 2, 3, 4–5, 6–8, 9–14, missing);
  - mean age = mean over the m − 1 agents with missing = 15.
* Monitors (thresholds fixed from calibration only):
  - S (support): flag iff the key occurred fewer than n_min = 3 times in calibration (sensitivity n_min = 1 and 10 reported);
  - F (freshness, the AoI reflex): flag iff mean age > the calibration 95th percentile of its time bin;
  - R (range on the scalar): flag iff mean age is outside [2.5th, 97.5th] percentile of its time bin.
* Systems per episode: RELAY (receiver everywhere), Z (Z everywhere), FB_S, FB_F, FB_R (flagged agents act with Z at that
  decision, the others with the receiver; the relay protocol state is untouched).
* Metric: gain vs Z in % = −(Σ queue_sys / Σ queue_Z − 1) × 100 per seed, mean over seeds; 95 % interval by the two-level
  bootstrap of scripts/MARL_e3_mixq_report.py (seeds, then traffic seeds).  Fallback rate = flagged share of agent-decisions.
* Self-checks that can fail (the run refuses to report otherwise): (i) a never-firing monitor reproduces RELAY and an
  always-firing monitor reproduces Z exactly on the first episode of every run; (ii) in the smoke, RELAY reproduces the saved
  test C rows (R_relayCK1_st_s0_K1, panel 4501) and Z the saved Z_s0 rows exactly; (iii) access invariants and the oracle guard
  as in the age-clip evaluator; (iv) source hashes unchanged during the run.

* AMENDMENT 1 (22:40, before any panel run; calibration-only evidence, training episodes 301–332, no panel episode used):
  with raw counts over 15 agents the 4×4 key is too fine — relayCage_st_s0's leave-one-episode-out false alarm at n_min = 3 is
  11.3 % (2 881 keys in 26 624 views) vs 0.9 % on 3×3.  The support key now counts on 8 PROPORTIONAL slots, every count c →
  round(8 c / (m − 1)): identical to the registered key on 3×3 (checked: same table for relay6Cage_st_s0), 1 491 keys and 5.2 %
  false alarm on 4×4 (F 4.6 %, R 2.1 %).  n_min = 3 and every prediction unchanged.  The eval reads the resolution from calib.json.

## Predictions (fixed now)
Hazard cell = (receiver, K) whose RELAY gain has 95 % upper bound < 0 on THIS panel; benefit cell = lower bound > 0.
Upgrade hazard cell = a hazard cell whose K is fresher than the receiver's training channel (relayCK1 at K ≥ 2 or iid).
* FB1 (repair) in every hazard cell, FB_S recovers at least half the deficit: gain(FB_S) ≥ ½ gain(RELAY).
* FB2 (little cost where it works) in every benefit cell at the receiver's own training channel (relay6Cage / relayCage at iid,
  relayCK1 at K1, relayMIX at all four, relayMIX2 at K1 and iid), gain(FB_S) ≥ 0.75 gain(RELAY).
* FB3 (support, not freshness) in every upgrade hazard cell, FB_S recovers ≥ ½ of the deficit and FB_F < ¼.  (If no upgrade
  hazard cell exists on a network, FB3 is not tested there; expected on 4×4: relayCK1 at iid, L-286.)
* FB4 (joint support vs a scalar range) the deficit recovered by FB_S summed over hazard cells ≥ that recovered by FB_R.
* FB5 (no new failure) in every cell gain(FB_S) ≥ min(gain(RELAY), 0) − 0.5.
* Reported: fallback rates per monitor and cell; calibration false-alarm of each monitor; n_min sensitivity.
Kill rule: if FB1 fails, the monitor-plus-fallback repair does not transfer from the C0 testbed (ledger C-3, fallback recovered
more than half) to a learned team.

## Outputs
scripts/MARL_e3_fallback_eval.py (calibrate / eval modes), scripts/RUN_marl_e3_fallback.sh, report
scripts/MARL_e3_fallback_report.py → research/marl_budget/e3_fallback_20261002/ (calib/*.json, cells, report.txt).  Smoke first.

## Addendum 2 (02/10/2026 23:0x EDT; the production lanes have run since 22:49 but NO panel row has been read)
* Omitted ancestor, now cited: the 01/10 SILENCE-FALLBACK GATE (scripts/MARL_e3_gate_eval.py; ledger L-214, L-221;
  PROTOCOL_E3_GATE_PROSPECTIVE_20261001): every intersection carried relay + Z; a hand-tuned FRESHNESS trigger (b₃ = Σ(age − 3)⁺
  > 6, chosen on the development panel) on relay6Cage at K = 1 on 3×3 only; GT3 SUPPORTED (+0.78 % vs plain), GT1 NOT
  (−0.59 % vs Z: half the loss repaired, the early sparse steps untouched).  This test differs in the trigger (support of the
  receiver's own training logs, calibrated, not tuned on any panel), the direction (upgrades, where a freshness trigger cannot
  fire), the receivers (four, incl. mixtures) and the networks (3×3, 4×4, NYC).  FB1's "half" is GT3's size.
* FB6 (registered now, from the failure synthesis research/papers/audits/FAILURE_SYNTHESIS_20261002.md, H3: what predicts
  harm is the share of deployment views outside the receiver's joint training support): within each network, over all
  (receiver, K) cells, Spearman(FB_S fallback rate, −gain(RELAY) vs Z) ≥ 0.6.
