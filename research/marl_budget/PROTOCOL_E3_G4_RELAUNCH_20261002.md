# 4×4 RELAUNCH — execution addendum to the 4×4 protocols (no change to any arm, recipe, panel, predictor or rule)

Written 02/10/2026 01:5x EDT (`date` 01:59:34 before writing), BEFORE the relaunch.  User 02/10 01:0x: after E1/E3/E5/E4,
"chạy 4x4 lại đi, tối ưu nó trc khi chạy".  Governs the execution of PROTOCOL_E3_G4_REPLICATION_20261001 (+ Addenda 1, 2) and
PROTOCOL_E3_G4_CONSTK_20261001 (+ Addenda 1–4); everything they fix stays fixed.  The chain was stopped 02/10 01:0x (L-245).

## State at writing (COMPLETE manifests)
Teachers set_full_s0, s1, s3, s4; s5 / s7 / s9 resumable (state_last.pt at iterations 1744 / 371 / 323); s2, s6, s8 absent
(s2's failed attempts are in legacy/).  Zero-byte students distill_none_s0, s4; distill_none_s3 partial (327 / 500, written
by the non-resumable trainer — no state, will be parked to legacy/ and retrained); s1 absent.  Relay students relayCage_st_s0,
s1, s3; s4 absent.  Replication evaluations complete for seed 0 (Rdev_s0_low, VD_s0, Z_s0, R_s0_iid, R_s0_low) and Z_s4.
Const-K outputs: none (the seed-0 development look of L-219 / L-247 lives elsewhere; target panel 3301–3364 unseen).

## What changes (execution only)
1. Student trainers: scripts/MARL_e3_actor_distill_v9.py replaces MARL_e3_actor_distill.py (zero-byte) and
   MARL_e3_actor_distill_v6.py (relay).  On the 4×4 wrappers v9 reproduces both bit for bit, weights and logs, and resumes
   exactly (scripts/TEST_marl_g4_students_v9.py PASS 01:53, L-253) — the recipe and its results are unchanged; a hang now
   resumes in place instead of restarting from iteration 0.  --park-if-no-state; watchdog WITHOUT --out, 20 retries.
2. Teachers: unchanged trainer (MARL_e3_actor_train_delivery_v6.py → MARL_e3_actor_train_resume.py, exact resume), now run
   WITHOUT the watchdog's --out (the old --out parked the directory on a stall and restarted from 0 — how set_full_s2 was
   lost); set_full_s5 / s7 / s9 continue from their states.  A teacher killed before its first state is parked to legacy/.
3. One dependency-aware scheduler (scripts/RUN_marl_g4_resumable.py; smoke-tested with fake jobs 01:59: dependencies,
   retry-once, exclusion of dependants, core cap) replaces the five fixed lanes and the serial downstream chain.  Core
   budget 10 (`--cores 10`; trainers weigh 2, evaluation jobs 1), so the machine is not oversubscribed (with the old lanes
   plus the concurrent E3 runs the 1-minute load reached ≈ 30–33 on 10 cores; a 4×4 relay student then took 23 339 s for
   500 iterations against ≈ 8 400 s for a 2 000-iteration teacher on the lighter 30/09 machine).  Priority: evaluation jobs first, then the work that completes seeds
   soonest (seed order 1, 3, 4, 5, 7, 9, 2, 6, 8).
4. Per-seed downstream work starts as soon as that seed is ready: the replication evaluations
   (scripts/RUN_marl_g4_seed_evals.sh), the margin probe (RUN_marl_g4_margin.sh's command) and the const-K development
   probes + target panel (scripts/RUN_marl_g4_constk_seed.sh = RUN_marl_g4_constk.sh's full-mode loop body; it contains the
   R5 development items NF iid / low).  All commands are copied verbatim; only their timing changes.
5. Reports (MARL_e3_g4_replication_report, MARL_e3_g4_r5_report, MARL_e3_g4_constk_report) run once, when every job has
   settled.  No target-panel statistic (panels 2901–2964, 3301–3364) is computed or looked at before that; check-ins report
   job states and training curves only.

## Unchanged
Arms, recipes (iterations, hyper-parameters, slots, codebook, order), panels, conditions, endpoints, predictors, R1–R3, R5,
the const-K rules G1–G8 and Addenda 1–4 predictions (incl. the provisioning rule A, prospective on the target panel), the
completeness rule (fewer than 8 complete seeds ⇒ INCOMPLETE; failures named).  Mixed producers are declared: seeds 0–4's
students were trained by the old trainers, the rest by v9; L-253 shows the two produce identical results.

## Expected duration
≈ 15 student trainings, ≈ 9 300 teacher iterations, 10 × (replication evals + margin + const-K): ≈ 100 core-weighted hours;
at a 10-core budget ≈ 12–20 hours (to be revised at the first check-ins from the measured iteration speed).

Addition 02/10 02:4x (`date` 02:49, still before the relaunch): disk.  E4 stopped at its disk guard (L-255).  The scheduler
now runs scripts/UTIL_dedupe_hardlink.py (byte-identical scenario files of FINISHED runs → hard links; nothing deleted; every
replacement logged) whenever free space is < 25 GB (at most hourly), and when it is < 15 GB it waits instead of starting a
job (it never exits early and never runs the reports while work is pending).  Re-smoked 02:48 with fake jobs: low disk →
dedupe → wait → resume; retry / exclusion / core cap as before.
