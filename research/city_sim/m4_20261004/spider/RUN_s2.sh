#!/usr/bin/env bash
# M4 stage 2: 2a rule eval on spider DEV + 2b R9 search (5 seeds) on spider TRAIN, all through CITY_m4s_run.py
cd /Users/phanan/cig-amf-main; D=research/city_sim/m4_20261004/spider; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; S="100 101 102 103 104 105 106 107 108 109"
R() { XPLAY_TMP=$PWD/$D/s2a/tmp nice -n 5 $PY -u scripts/CITY_m4s_run.py "$@" --light FT --seeds $S --out $D/s2a >> $D/s2a/run.log 2>&1; }
R scripts/CITY_eval6_lane.py --fleet GLOSAL:0.3 --tag GLOSALS & R scripts/CITY_eval6.py --fleet GLOSA --tag GLOSA_FT &
R scripts/CITY_eval4.py --fleet L-ACT:0 --guard always --tag OFF_FT & R scripts/CITY_eval4_sigma.py --sigma 0.3 --fleet L-ACT:0 --guard always --tag S0.3_FT &
for s in 1 2 3 4 5; do XPLAY_TMP=$PWD/$D/s2b/tmp nice -n 5 $PY -u scripts/CITY_m4s_run.py scripts/CITY_glosa_lane_d.py search $s $D/s2b/theta_s$s.json > $D/s2b/search_s$s.out 2>&1 & done
wait; $PY scripts/CITY_m4_s2a_report.py; echo "stage2 a+b done $(date)"
