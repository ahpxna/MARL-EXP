# Protocol deviation note — E3 actor seeds (dated 28/09/2026, 14:06; independent recheck P1)

This note is written after the fact and is not backdated.
- It amends nothing. PROTOCOL_E3_PILOT and PROTOCOL_E3_SCRATCH stay as written, and their seed lists stay
  "0, 1, 2".
- It records the deviation and the reporting commitments that now bind every E3 report.
- E3_PROVENANCE_NOTES_20260928.md §1 is superseded by this note where they differ.

## 1. The deviation

Seeds 3 and 4 of both recipes were launched at 00:49 on 28/09, under the protocols' own hashes. The runs are
`e3_run_seeds34_20260928` (warm-started, BC + MAPPO) and `e3_scratch_seeds34_20260928` (scratch). No protocol
lists these seeds.

**What the early launch does rule out.** At 00:49 no label, selector or closed-loop result existed, so the
launch seeds were not chosen after seeing outcomes.

**What it does NOT rule out.** It does not rule out later selective reporting, stopping or checkpoint choices.
The commitments in §3 exist for that.

## 2. Every actor seed, as of 14:06 (development evidence only)

**Warm-started recipe.** Gate rule: G1/G2 on the PILOT seed s0 decides whether the recipe's selector results are
read.

| seed | actor | G1 on its own |
|---|---|---|
| s0 (pilot) | done, select 1462 | **FAIL** (none +0.4%) → the recipe's selector results are recorded, not read |
| s1 | done, select 1490 (retrained after the pipefail stop) | PASS (+11.3%) |
| s2 | NOT STARTED (lane D runs it after s1's labels) | — |
| s3 | done, select 1451 | PASS (+5.7%) |
| s4 | done, select 1460 | PASS (+17.5%) |

**Scratch recipe.** Gate rule: per seed.

| seed | actor | G1 |
|---|---|---|
| s0 | lane-2 attempt 2 at iteration ~994. Replica in `e3_scratch_rs_20260928` since 14:03 | — |
| s1, s2 | never trained in the lanes. Replicas in `e3_scratch_rs_20260928` since 14:03 | — |
| s3 | done, select 1316 | PASS (+7.3%) — **the only gated scratch actor so far** |
| s4 | lane-C attempt 3 (the LAST watchdog retry) at iteration ~171. Replica since 14:03 | — |

**Mixed-profile recipe (pilot, one seed).** s3 is training, at iteration ~1180 of 2000.

**Failed or parked training attempts** (kept in `legacy/`, never deleted; infrastructure failures, not results):
- `actor_s0_stalled_0_20260928_124925`, `actor_s0_stalled_1_20260928_130525`: scratch s0 hangs;
- `actor_s4_stalled_0_20260928_110940`, `_0_20260928_122310`, `_1_20260928_125211`, `_2_20260928_134442`:
  scratch s4 hangs, reaching iterations ≈ 510 / 137 / 997 before the hang;
- `research_marl_budget_e3_scratch_20260928_0043_actor_s0_partial_20260928_113642` and
  `…seeds34_20260928_actor_s4_partial_20260928_114038`: parked at the 11:37 pkill.

The replicas use `scripts/MARL_e3_actor_train_resume.py`, which is bitwise-equivalent to the protocol trainers
(tested). Their run-of-record rule was fixed before any outcome: `e3_scratch_rs_20260928/RUN_OF_RECORD_RULE.md`.

## 3. Reporting commitments (binding from now on)

1. **Every seed is reported.** Every actor seed that completes is reported with its G1/G2 outcome and every
   downstream result, whatever its sign. A seed that never completes is reported with the reason.
2. **Gates are read as registered.** The warm-started recipe is gated on s0, which failed, so its selector
   results are never called confirmatory or "read". The scratch recipe is gated per seed.
3. **The pass rate always goes with a subgroup.** A result on a gated subgroup is always stated with the gate pass
   rate, and as conditional on the gate.
4. **Checkpoints are fixed.** The checkpoint of every actor is `ckpt_best.pt` (greedy select-split Σ waiting),
   as registered. No other checkpoint is chosen after seeing selector results.
5. **No early stopping.** No actor run is stopped early or extended because of its downstream results. Training
   length is 2000 iterations (scratch, mix) or 30 + 20 + 300 (warm-started).
6. **Aggregation.** Aggregation over actor seeds treats actor seeds as the replication unit. Selector init seeds
   are averaged within an actor and are not actor replications.
7. **The final protocol.** The final protocol (F6) lists every actor seed and the rule for gate failures BEFORE
   seeds 1301–1316 are opened.

**Update 15:32.** Two more lane-run losses, both infrastructure failures, not results:
- scratch s4 lane-C run: dead at 14:42:54 after its 4th hang (retries exhausted); the last attempt had reached iteration ~560;
- scratch s0 lane-2 run: hung at iteration ~1943, restarted from scratch at 15:25:36 on its last retry; parked in
  `legacy/actor_s0_stalled_2_20260928_152536`.
The resumable replicas continue; their traces were identical to the lane runs while both lived. BC s2 is finished and passes G1.
