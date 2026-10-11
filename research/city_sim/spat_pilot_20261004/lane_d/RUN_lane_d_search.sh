#!/usr/bin/env bash
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; D=research/city_sim/spat_pilot_20261004/lane_d; export XPLAY_TMP=$PWD/$D/tmp
for s in 1 2 3 4 5; do nice -n 5 external_envs/city_runtime/bin/python -u scripts/CITY_glosa_lane_d.py search $s $D/theta_s$s.json > $D/search_s$s.out 2>&1 & done
wait; echo "R9 search done $(date)"
