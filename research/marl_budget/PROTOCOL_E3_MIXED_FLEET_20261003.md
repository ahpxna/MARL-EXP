# PROTOCOL — mixed-version fleet PILOT, 03/10/2026 20:1x EDT

Written before any mixed-team run.

**Source.** The external audit P2_COMPLETED_EVIDENCE_AUDIT_20261003 §6 and its pilot steps 1–5.

**Status: PILOT.** Its only job is to decide whether to open a fresh multi-seed confirmation. It is not a benchmark win.
Panels 5301 (P1) and 5401 (P2) are not reused as tests here.

## 1. Question

After a capacity upgrade, half the intersections keep the legacy receiver (CK1, trained on K1) and half run a receiver
trained for the upgraded channel (Cage, trained on the deployed iid channel). Which deployment option is best for the WHOLE
network, without transferring harm to one group, and at what cost?

## 2. Team composition (fixed now, from topology only)

* 4×4 grid, agents in row-major order of intersection_r_c (taken from env.agent_ids).
* **OLD group: 50 % of agents**, in two layouts:
  * D (dispersed): checkerboard, (r + c) even, 8 agents;
  * C (clustered): the two left columns, c ∈ {1, 2}, 8 agents.
* **NEW group:** every other agent runs Cage. Cage is the primary new receiver; MIX is not run in this pilot.
* For a given actor seed s, every checkpoint used (CK1, Cage, Z) is that seed's.

## 3. Arms

Every arm runs on the same mixed team. All histories come from the real rollout of that arm's joint policy, with the same
physics.

| Arm | Channel | OLD agents | NEW agents |
|---|---|---|---|
| U1/PLAIN | U1 (deployed iid, adaptive order) | plain | plain |
| U2/PLAIN | U2 (order-preserving iid; NestedDelivery from P2) | plain | plain |
| U2/EMU_OLD | U2 | near-exact emulator of the legacy view (P2's Exact) | plain |
| U1/FB_OLD | U1 | FB_S+ fallback to their own Z (detector frozen in P1: e3_repair_panel_20261003/4x4/det_relayCK1_st_s/detectors.json) | plain |
| K1/ROLLBACK | K1 for the whole network (const1) | plain | plain |

Mixed-team arms share one shape: the channel's merged views, then each agent's own receiver.

**FB_S+ was chosen now from earlier evidence** (4901: it blocks the upgrade harm), not from P1. FB_S+ calibration was
frozen before any P1 panel episode.

**References** (quality / cost, not the same deployment budget):

* ALLNEW: every agent is Cage on U1. This is retrain-all; its cost is retraining 8 receivers.
* ALLOLD: every agent is CK1 on K1. This is the legacy system before the upgrade.
* ZTEAM: every agent is Z (delivery none). This is the silent baseline of every gain.

## 4. Panel

* Traffic seeds 5901–5932 × {8, 16}: 64 episodes, checked unused at 20:1x.
* Actor seeds 0–4.
* Both layouts.

## 5. Endpoints

| | Definition |
|---|---|
| Primary | System gain vs ZTEAM: −(Σ queue / Σ queue of ZTEAM − 1)·100, per actor seed. Two-level crossed bootstrap (2000, rng 0). |
| Secondary: old-group local gain | The same, restricted to the OLD intersections' own queues (per-agent queue = waiting on that agent's incoming lanes, measured after each step, outside every policy). |
| Secondary: new-group local gain | The same, restricted to the NEW intersections. |

Also reported:

* delivered bytes (delivered direct packets × 25 B);
* emulator buffer size;
* runtime per episode;
* the number of receivers retrained: 0 for every mixed arm, 8 for ALLNEW.

There is no per-junction safety guarantee drawn from system totals.

## 6. Pilot GO rule

For each layout, at the pilot level (5 seeds), GO to confirmation if all of these hold:

1. U2/EMU_OLD − U2/PLAIN > 0 on the system endpoint, with CI lower > 0.
2. U2/EMU_OLD − U1/FB_OLD > 0 on the system endpoint, with CI lower > 0. Alternatively, U2/EMU_OLD keeps more old-group
   local gain than U1/FB_OLD at no larger byte cost.
3. New-group local gain of U2/EMU_OLD ≥ that of U1/PLAIN − 0.5. This is a point-estimate screening margin, not
   non-inferiority.

The pilot also reports, without a verdict:

* U2/EMU_OLD − K1/ROLLBACK;
* U2/EMU_OLD − ALLNEW;
* U2/EMU_OLD − ALLOLD.

## 7. Self-checks

The run refuses to write a manifest if any of these fails.

* On the first episode of each job:
  * OLD = all agents with arm U1/PLAIN equals homogeneous CK1 PLAIN (scripts/MARL_e3_repair_panel_eval.run_arm);
  * OLD = none equals homogeneous Cage PLAIN;
  * OLD = all with U2/EMU_OLD equals P2's U2/EXACT episode total.
* The per-agent queues sum to the step queue at every step.
* Access invariants, the oracle guard and source hashes hold.

## 8. Smoke and freeze (20:07 EDT, before the pilot launch)
Smoke (seed 0, traffic 9001-9002; NOT evidence): identities PASS (ZTEAM = run_z, OLD = all = CK1 PLAIN, OLD = none = Cage PLAIN, OLD = all EMU = P2 U2/EXACT); per-agent queues sum to the step queue; pipeline through the report.  Frozen (sha256, first 16 hex):
* MARL_e3_mixed_fleet_eval.py 6a8ce4daf1496e0c
* RUN_marl_e3_mixed_fleet.sh d8220dab2c74c1d0
* QUEUE_marl_e3_mixed_fleet_20261003.sh f252bca8699c939c
* MARL_e3_mixed_fleet_report.py 9dc23df6e6b25028
* MARL_e3_p2_nesting_replay.py ff4e88922b0be3f7
* MARL_e3_repair_panel_eval.py db7ceb9284d42999
Launch: chained after the adaptation pilot queue (LANES=3, nice 10).
