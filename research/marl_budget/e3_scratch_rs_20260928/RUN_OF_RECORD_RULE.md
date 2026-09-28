# Scratch-recipe actors trained with the resumable, bitwise-equivalent trainer (28/09/2026, declared at 14:03, before any outcome)

- Trainer: `scripts/MARL_e3_actor_train_resume.py`. Equivalence tested at 13:55: with the same arguments it gives
  ckpt weights IDENTICAL to `MARL_e3_actor_train.py` (scratch) and to `MARL_e3_actor_train_mix.py` (mix). A run
  stopped at iteration 2 and resumed in place is identical to an uninterrupted run. The mix test is not vacuous:
  its weights differ from scratch.
- Arguments: those of PROTOCOL_E3_SCRATCH / `RUN_marl_e3_resume_v3.sh`, i.e. `--iters 2000 --eps-per-iter 8
  --eval-every 20`, default threads 2.
- Watchdog: run WITHOUT `--out` (in-place resume), stall 900 s, retries 50.

**Seeds and why they are here.**
- **s4** replicates the lane-C run `e3_scratch_seeds34_20260928/actor_s4`. That run lost ~1,640 iterations to
  three hangs (restarts at 12:23, 12:52 and 13:44) and is on its LAST watchdog retry.
- **s0** replicates the lane-2 run `e3_scratch_20260928_0043/actor_s0`, which has 1 retry left.
- **s1 and s2** are protocol seeds that lane 2 never reaches, because `RUN_marl_e3_resume.sh` v1 stops after
  training s0 (the known pipefail defect).

**Run of record, per seed (fixed now, independent of any outcome).**
1. The first run of that seed that completes 2000 iterations is used.
2. If both the lane run and the replica complete, their final checkpoints must be identical. If they are not
   (for example through thread-level floating-point nondeterminism), the LANE run is the run of record.
3. Every run is reported, including failed and stalled attempts (parked in `legacy/`).

**Live check (at 14:12).** The lane runs and the replicas started from the same seed, and they print IDENTICAL
training traces on every iteration they have in common:
- s4: 77/77 iterations identical, lane-C attempt 3 vs `actor_s4`;
- s0: 76/76 iterations identical, lane-2 attempt 2 vs `actor_s0`.
The fields compared are train Σwait, entropy and value loss. So far the two runs of a seed are the same actor.
