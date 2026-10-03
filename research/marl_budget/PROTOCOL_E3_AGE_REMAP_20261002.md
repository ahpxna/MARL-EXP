# Pre-specified test: a TRAINING-FREE age remap repairs upgrades fully and downgrades only partly (the direction asymmetry)

Written 02/10/2026 11:5x EDT (`date` 11:58:38 before writing), BEFORE any run below.  User 11:5x: "làm 1, 2, 4" (round-10
direction, MARL_DIRECTION_ROUND10_20261002.md, step 1).

## Idea
A learned receiver's value follows W1(deployment age distribution, training age distribution) (L-249, L-258).  A
receiver-side interface can remove that distance without retraining: relabel every present entry's age by the monotone
optimal-transport coupling from the deployment age histogram p to the training histogram q (content unchanged, protocol
state unchanged — only what the actor reads; as the age clip of PROTOCOL_E3_AGECLIP_PROSPECTIVE).  The DIRECTION matters:
* UPGRADE (deployment fresher than training: relayCK1, trained at const K = 1, deployed at K = 2, 3, iid): fresh content is
  shown with OLDER labels — the receiver under-trusts information that is in fact better — predicted to recover (most of)
  its training-channel performance or more.
* DOWNGRADE (deployment staler: relay6Cage, trained iid, deployed at K = 1, 2, 3): stale content is shown with FRESH labels —
  the receiver over-trusts it — predicted to help only partly (the age clip, a coarse version, closed ≈ half the K = 1 gap).
Network-side counterpart, by construction: under an upgrade the network can EMULATE the training channel exactly (decode
only K_train packets), so the emulation value = relayCK1's own gain at K = 1 on the same panel (measured below); under a
downgrade no scheduler can (the receiver floor).

## Remap (fixed now)
Histograms: channel-only g3_nopolicy merged-view age histograms (research/marl_budget/e3_channel_composition_20261001/
g3_nopolicy/composition.json, ages 0–14, present entries only; at constant K and under age-first they do not depend on the
policy).  Coupling: an entry of deployment age a gets u ~ Uniform(F_p(a − 1), F_p(a)] and label F_q⁻¹(u) (the exact
monotone transport plan, so the relabelled marginal equals q); u from a deterministic hash of (traffic seed, headway,
step, receiver, sender) so runs are reproducible.  Only ages change (present entries stay present; never-heard stay absent:
the coverage difference is NOT removed — stated limitation).  At the training channel itself the map is the identity
(SELF-CHECK: relayCK1 at K = 1 and relay6Cage at iid with the remap must reproduce the plain rows exactly).

## Design
Panel 4001–4064 × headways 8 / 16 (checked unused 11:43 by parsing all 210 444 manifest / config files), used once.
Students seeds 0–4: relayCK1_st_s<s> and relay6Cage_st_s<s>; Z = distill_none_s<s>.  Evaluator scripts/MARL_e3_ageremap_eval.py
(= MARL_e3_ageclip_eval.py + --remap TRAIN, a new file; the clip path is kept).  Cells:
plain (--remap none): both students at K = 1, 2, 3, iid; remap: relayCK1 at K = 2, 3, iid (train K1), relay6Cage at
K = 1, 2, 3 (train iid); identity checks: relayCK1 at K = 1 and relay6Cage at iid with the remap; clip A = 2 for relay6Cage
at K = 1 (the earlier repair, same panel); Z.  Endpoint, pairing, two-level bootstrap as PROTOCOL_E3_TRAIN_MATCH_K1.

## Predictions (mean over seeds 0–4)
- RM1 (upgrade repaired): relayCK1 at iid, remap vs plain effect > 0 with bootstrap lower bound > 0.
- RM2 (upgrade, all cells): remap ≥ plain for relayCK1 at K = 2, 3 and iid (means).
- RM3 (asymmetry): recovery fraction f = (remap − plain) / (retrained specialist − plain), with the retrained specialist =
  relay6Cage for iid / K = 2 / K = 3 and relayCK1 for K = 1 (each cell's best training-matched receiver on the same panel;
  gains vs Z).  Upgrade cells (relayCK1 at iid): f ≥ 0.7.  Downgrade cell (relay6Cage at K = 1): f ≤ 0.5.
- RM4 (downgrade, reported, sign only): relay6Cage at K = 1, remap vs plain > 0; compared with the clip on the same panel.
- RM5 (exploratory): relayCK1 with the remap at iid ≥ its plain K = 1 gain (fresher content under its own label
  distribution beats its emulated training channel).
Reading fixed now: RM1–RM3 → the repair of a learned receiver's channel shift depends on the DIRECTION of the shift, as the
emulation lemma + floor predict on the network side; a training-free interface fixes upgrades, not downgrades.  RM1 failing
→ age labels are not the channel through which upgrades hurt (coverage / content distribution is).  Exploratory: n = 5.
Launcher scripts/RUN_marl_e3_age_remap.sh and report scripts/MARL_e3_age_remap_report.py written before the run.
