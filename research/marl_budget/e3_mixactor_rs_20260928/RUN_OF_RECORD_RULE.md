# Mixed-profile actor s3: resumable replica (28/09/2026, rule written at 15:32:25, BEFORE the replica is launched)

- Trainer: `scripts/MARL_e3_actor_train_resume.py --p-mix 0.5`. It is bitwise-equal to `MARL_e3_actor_train_mix.py` with the same
  arguments, uninterrupted and stopped-then-resumed; the test is in `e3_scratch_rs_20260928/RUN_OF_RECORD_RULE.md`.
- Arguments of the lane run (PROTOCOL_E3_MIXACTOR): `--seed 3 --iters 2000 --eps-per-iter 8 --eval-every 20 --p-mix 0.5`.
- Why: the lane run `e3_mixactor_20260928/actor_s3` (old trainer, no resume) is at iteration ~1850 of 2000. A CityFlow hang now
  would restart it from scratch, as it did for scratch s0 at 15:25 and for scratch s4 four times.
- **Run of record (fixed now):** the first of the two runs to complete 2000 iterations. If both complete, their final
  checkpoints must be identical; if they are not, the LANE run is the run of record. Both runs are reported.
