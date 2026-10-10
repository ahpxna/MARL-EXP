#!/usr/bin/env bash
# M2b: RL-H:k phase traces with σ* cars, TRAIN 0-7 (fit) and SELECT 100-104 (validation)
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/spat_pilot_20261004/m2b/traces; export XPLAY_TMP=$PWD/$D/tmp
for k in 0 1 2 3; do
  nice -n 5 $PY -u scripts/CITY_eval4_sigma.py --sigma 0.3 --light RL-H:$k --fleet L-ACT:0 --guard always --seeds 0 1 2 3 4 5 6 7 --record $D/rlh${k}_s{seed}.npz --tag fit_RLH$k --out $D >> $D/run.log 2>&1 &
  nice -n 5 $PY -u scripts/CITY_eval4_sigma.py --sigma 0.3 --light RL-H:$k --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --record $D/rlh${k}_s{seed}.npz --tag val_RLH$k --out $D >> $D/run.log 2>&1 &
done; wait; echo "traces done $(date)"
