# PROTOCOL — joint-level garbling (receiver-side throttle to the training capacity) and the masked-message reference
Written 03/10/2026 10:5x EDT (day wake 1), after two smokes on non-panel seeds (values below), BEFORE any panel run.
Script scripts/MARL_e3_joint_throttle_eval.py; launcher scripts/RUN_marl_e3_joint_throttle.sh; queue
scripts/QUEUE_marl_e3_joint_throttle_20261003.sh; report scripts/MARL_e3_joint_throttle_report.py.

## Question
L-295: garbling ENTRIES back into per-slot / per-rank support beats a relabel (EMU > LAB) but does not repair the upgrade
hazard; the hazard lives in the JOINT view configuration (L-272, L-293 FB3: the joint-support monitor recovers it fully).
Here the garbling acts at the joint level: a receiver trained at capacity k_train accepts at most k_train delivered packets per
step (age-first: the neighbour whose last accepted packet is oldest), and its view is built with the ACTIVE merge rule (relay v2,
or the grid wrapper's slot-restricted merge) from the accepted packets and its own shadow cache — the receiver-side emulation of
its training reception given what the others transmit (the others' packets still come from the upgraded world).  Control
THRLAB: the PLAIN payloads shown with THR's per-sender ages.  MASK: the same receiver with all messages removed — the CGDC-style
masked-message reference π^(−0), compared with our compiled-silent bar Z.
## Design
Panel 5201–5264 × 8/16 (new).  4×4 (grid relay wrapper, nearest8) seeds 0–9, 3×3 seeds 0–4.  relayCK1_st (k_train = 1) at
K ∈ {1, iid, 2, 3}, modes plain / thr / thrlab / mask; the iid-trained receiver (relayCage_st / relay6Cage_st) at K ∈ {iid, 1},
modes plain / mask; Z_s on the panel.  Gain vs Z = −(ΣR/ΣZ − 1)·100 per seed, bootstrap over seeds and traffic seeds.
Self-checks: k_train = ∞ ⇒ the shadow merge equals the active merge exactly at every step of the first episode (views and encoded
inputs) and the episode equals PLAIN; at K = 1 THR ≡ PLAIN (nothing to drop: asserted in the report); source / checkpoint hashes.
## Predictions (fixed now)
* JT1 (joint repair, 4×4 relayCK1 at iid): gain(THR) − gain(PLAIN) > 0, lower bound > 0, ≥ 7/10 seeds.
* JT2 (H1 contrast, 4×4, iid): gain(THR) − gain(THRLAB) > 0, lower bound > 0, ≥ 7/10 seeds.
* JT3 (masked reference understates the bar): gain(MASK) vs Z < 0 with upper bound < 0 for relayCK1 at K = 1 and the iid-trained
  receiver at iid, on both networks (a messaging receiver with its messages masked is worse than the compiled-silent student).
* JT4 (3×3 replication): signs of JT1 and JT2 in ≥ 4/5 seeds.
* Reported: K = 2, 3; dropped-packet counts; THRLAB − PLAIN; THR vs the matched iid-trained receiver.
Kill / reading rules: JT1 failing with JT2 holding ⇒ the throttled direct reception alone does not restore the support (the
relayed content from the upgraded world keeps the view out of support) — repairs must change the receiver (training) or switch
actor (fallback).  JT2 failing ⇒ even joint garbling gives no advantage over relabelling: H1 not supported at the joint level.
Smoke disclosure (non-panel seeds 9001–9002 × 8, seen): 3×3 relayCK1_s0 iid PLAIN 1786 / 1734, THR 1670 / 1619, THRLAB 1882 /
1760, MASK 1670 / 1786; 4×4 (9001 × 8) PLAIN 1841, THR 2153, THRLAB 2078, MASK 2192 (queue sums, lower is better; not evidence).
## Novelty / scope
Receiver-side throttling is an engineering trick (a de-jitter / rate-limit buffer); the contribution is the test of where the
support lives.  Simulation only; our own receivers; no real controller logs, J2735 traces, independent stack or real
cross-version data.
Pipeline smoke (10:5x, seed 0, traffic 9001–9002 × 8/16, seen; not evidence): 4×4 iid THR − PLAIN −11.48, THR − THRLAB −1.66,
MASK −14.01 vs Z; 3×3 iid THR − PLAIN +4.14, THR − THRLAB +7.25, MASK +2.54 vs Z.  Predictions above unchanged.
