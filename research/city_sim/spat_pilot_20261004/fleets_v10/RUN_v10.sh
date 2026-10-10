#!/usr/bin/env bash
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; P=research/city_sim/spat_pilot_20261004/fleets_v10
for s in ${SEEDS:-13 113 213 313}; do
  nice -n 5 external_envs/city_runtime/bin/python -u scripts/CITY_fleet_train_v10_ppo.py --spat on --seed $s --episodes 400 --name R10_s$s --out $P --resume >> $P/R10_s$s.out 2>&1 &
done
wait; echo "v10 done $(date)"
