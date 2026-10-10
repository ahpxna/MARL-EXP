#!/usr/bin/env bash
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; D=research/city_sim/spat_pilot_20261004/fleets_v11
for s in 13 113 213 313 413 513; do nice -n 5 external_envs/city_runtime/bin/python -u scripts/CITY_fleet_train_v11_ppo.py --spat on --seed $s --episodes 400 --name L11_s$s --out $D --resume > $D/L11_s$s.out 2>&1 & done
wait; echo "v11 training done $(date)"
