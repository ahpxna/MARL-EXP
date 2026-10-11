# PROTOCOL — cross-channel negative flips of frozen receivers on identical states (EXPLORATORY diagnostic)
Written 03/10/2026 04:1x EDT (wake 2), after a 1-episode smoke (seed 0, traffic 901 × 8 — values below), before the full run.
Why: reviewers will import Bansal / PCT / Srivastava compatibility metrics (LITERATURE_DEEP_READ_20261003); E3 had no action logs
of one receiver on IDENTICAL states under two channels (train × deploy matrix README, finding 5).
Design: scripts/MARL_e3_crosschannel_flip_probe.py — Z drives from its local view (the world is identical under every channel;
self-check), each channel (const1, const2, const3, iid; age-first prefix; relay v2) builds merged views; receivers are evaluated,
never executed; acceptability = teacher A_0.25 on the full fresh counterfactual view (diagnostic oracle, recorded only; identical
across channels — self-check).  Development episodes 901–904 × 8/16 (diagnostic, used before by the negflip / age-response
probes; not a target panel).  3×3 seeds 0–4: relay6Cage_st, relayCK1_st, relayCK2_st, relayMIX_st, relayMIX2_st; 4×4 seeds
0–9: relayCage_st, relayCK1_st (4×4 relayMIX = test D, not opened).  States are Z's closed-loop states, not the receiver's own.
Predictions (net = PF − NF):
* FL1 relayCK1 const1 → iid: net < 0 in ≥ 4/5 (3×3) and ≥ 8/10 (4×4) seeds.
* FL2 iid-trained (relay6Cage / relayCage) iid → const1: net < 0 in ≥ 4/5 and ≥ 8/10 seeds.
* FL3 relayMIX const1 → iid: net ≥ 0 in ≥ 4/5 seeds (3×3).
* FL4 BTC(relayCK1, const1 → iid) < BTC(relayMIX, const1 → iid) in ≥ 4/5 seeds (3×3).
Reported: every pair, agreement, accuracy per channel; relayCK2 (peaked expectation).
Smoke (seen): s0, 1 episode — CK1 const1→iid NF 0.107 PF 0.030 BTC 0.884; 6Cage const1→iid net +0.06; MIX +0.013; MIX2 +0.004.
Limits: simulation, our own receivers; no real controller logs, J2735 traces, independent stack, or real cross-version data.
