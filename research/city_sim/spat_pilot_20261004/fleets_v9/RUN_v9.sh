#!/usr/bin/env bash
# v9 training launcher (Amendment R4): 6 seeds in parallel, 400 episodes, resumable.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; P=research/city_sim/spat_pilot_20261004/fleets_v9
for s in 13 113 213 313 413 513; do
  nice -n 5 external_envs/city_runtime/bin/python -u scripts/CITY_fleet_train_v9_ppo.py --spat on --seed $s --episodes 400 --name R9_s$s --out $P --resume >> $P/R9_s$s.out 2>&1 &
done
wait; echo "v9 done $(date)"
