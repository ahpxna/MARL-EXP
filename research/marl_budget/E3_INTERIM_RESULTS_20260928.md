# E3 interim results (28/09/2026, 03:00) — gates G1/G2 for the actors finished so far

- Protocols: `PROTOCOL_E3_PILOT_20260928.md` (BC + MAPPO) and `PROTOCOL_E3_SCRATCH_20260928.md`
  (MAPPO from scratch), both written before these results.
- Development split 501–508 × headways 8, 16 (16 episodes, opened); `scripts/MARL_e3_message_use.py`.
- **Self-checks PASS for every actor:**
  - access invariants on every step;
  - about 1,600 undelivered-sender blocks verified to be the missing encoding.
- **Operational note.** The Mac slept between about 00:55 and 02:50. The runs paused and did not
  fail (the logs' clocks count only awake time). `caffeinate` now holds the machine awake for 12 h.

## Actors finished so far

| actor | select Σ waiting (MP2 1730) | G2 (≤ +10% of MP2) | dev: MP2 vs actor | none vs actual | stale | shuffle | full | input change (none / stale / shuffle) | G1 |
|---|---|---|---|---|---|---|---|---|---|
| BC + MAPPO seed 0 (**pilot gate**) | 1462 (BC only 1624) | PASS | +12.1% [+7.1, +17.0] | +0.41% [−2.12, +2.86] | +2.27% [−0.55, +5.12] | +2.13% [−0.03, +4.16] | +6.39% [+2.31, +10.05] | 0.25 / 0.16 / 0.20 | **FAIL** (closed-loop part) |
| BC + MAPPO seed 3 | 1451 (BC only 1648) | PASS | +14.0% [+8.2, +19.9] | +5.68% [+2.13, +9.59] | −0.98% [−3.26, +1.31] | +0.98% [−1.91, +4.00] | +12.86% [+7.29, +19.21] | 0.29 / 0.18 / 0.21 | PASS |
| scratch seed 3 | **1316** | PASS | **+23.1% [+14.7, +31.9]** | **+7.31% [+4.05, +10.62]** | +1.14% [−2.52, +4.58] | **+5.06% [+2.26, +7.91]** | +2.47% [−0.38, +5.41] | 0.53 / 0.38 / 0.43 | PASS |

Columns "MP2 vs actor" through "full" are the paired change in closed-loop Σ waiting against the
same actor's `actual` run. Positive means worse than `actual`.

## Reading, as the protocols fix it

1. **Competence (G2).**
   - Every finished learned actor beats MP2: select −15% to −24%, and on development MP2 is
     +12% to +23% worse, with every CI above 0.
   - This is development evidence on a fixed panel, not a test.
   - The actor is learned (MAPPO on the team reward), and the scratch actor is not warm-started
     from MP2.
2. **Message use (G1).**
   - **The BC + MAPPO pilot seed 0 FAILS the closed-loop part of G1.** Removing all messages does
     not measurably hurt it (+0.4%), although 25% of its input-level actions change.
   - By PROTOCOL_E3_PILOT §5, the BC chain's selector and closed-loop results are therefore
     RECORDED BUT NOT INTERPRETED as a method result.
   - Seed 3 of the same recipe does pass. Message use varies across seeds.
3. **The scratch actor (seed 3) uses messages clearly.**
   - Removing them costs +7.3%.
   - Scrambling sender identity costs +5.1%.
   - Its gates are per seed (PROTOCOL_E3_SCRATCH), so its downstream results will be read.
   - The protocol's scratch gate for interpretation is per seed, and seed 0 of the scratch chain
     is still training.
4. **"Full" communication (every receiver decodes all 8 senders) HURTS the BC actors** (+6% and
   +13%). They never saw full delivery in training (capacities ≤ 7). This is a train/test
   distribution shift, so more information is not automatically better for a fixed actor
   (PROTOCOL_HETERO_v0 Amendment 1).

## Still running (03:00)

- BC + MAPPO seeds 0–2: labels for seed 0.
- BC + MAPPO seeds 3–4: labels for seed 3.
- Scratch seeds 0–2: seed 0 is training.
- Scratch seeds 3–4: labels for seed 3.
- Gates full9, then OLD7b.

## Update 08:30 — hung CityFlow processes; learned SchedNet baseline (partial)

**Hang.** Every E3 Python process stopped writing between 00:56 and 03:18 and has since sat at
0% CPU in state S. The Mac was kept awake after 02:53, and the Lean gates kept running.
- `sample` shows the main thread blocked inside `cityflow.cpython-312-darwin.so` in
  `pthread_cond_wait`: the engine's thread barrier, holding the GIL.
- Threads are few (12–18 per process), so this is not a thread leak.
- Reading: a lost-wakeup deadlock in CityFlow's barrier, exposed by heavy CPU oversubscription
  (about 25 processes on 10 cores) and the system sleep.
- Earlier runs (thousands of replays, all closed-loop panels) never hung.
- **Fixes:**
  - `scripts/run_with_watchdog.py`: kills a child whose log is silent for S seconds, parks its
    partial output in `legacy/` and retries. Tested on hang, success and failure.
  - `scripts/RUN_marl_e3_resume.sh` and `RUN_marl_e3_schednet_resume.sh`: keep every finished
    stage and rerun the rest under the watchdog, with the ORIGINAL shard partition.
- The hung processes must be stopped first; the resume runners refuse to start while they are
  alive.
- **What was complete at the hang:**
  - BC s0: actor, message use, select labels, train shards 1, 3, 4.
  - BC s3: actor, message use, dev labels, all 3 train shards.
  - Scratch s3: actor, message use, select and dev labels, train shards 0 and 1.
  - Scratch s0: nothing (hung at iteration 485 of 2000).

**Learned SchedNet adaptation** (`scripts/MARL_e3_schednet_train.py`; sender-side 1 B weight from
its own sensor; Plackett–Luce PPO on the team reward; frozen scratch-s3 actor; pilot panel 901–916;
against the same actor's cached-queue prefix):

| init seed | Σ waiting vs prefix |
|---|---|
| s0 | +1.13% [−0.66, +2.93] |
| s1 | +1.90% [−0.13, +4.25] |
| s2 | hung, to be rerun |

- The learned scheduling order does not beat the cached-queue prefix; it is slightly worse and
  not significant.
- The same run for the BC-s3 actor has not started yet.
