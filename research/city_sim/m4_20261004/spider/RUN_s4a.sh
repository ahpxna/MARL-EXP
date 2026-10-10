#!/usr/bin/env bash
# M4 stage 4a panel (Amendment M4-A6): WCK-5 commit / shadow on spider 1000-1019 for both lights, then the report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; SP=research/city_sim/m4_20261004/spider; E=$SP/s4/eval
mkdir -p $E/tmp; export XPLAY_TMP=$PWD/$E/tmp; S="$(seq -s ' ' 1000 1019)"
for k in 11 111; do
  nice -n 5 $PY -u scripts/CITY_m4s_wck.py --spat-mode commit --light WCK:$SP/RLK_sp$k.pt:5 --fleet GLOSAL:0.3 --seeds $S --tag WCK5_RLK$k --out $E >> $E/run.log 2>&1 &
  nice -n 5 $PY -u scripts/CITY_m4s_wck.py --spat-mode none --light WCK:$SP/RLK_sp$k.pt:5 --fleet GLOSAL:0.3 --seeds $S --tag WCK5sh_RLK$k --out $E >> $E/run.log 2>&1 &
done; wait; $PY scripts/CITY_m4_s4a_report.py; echo "M4 4a done $(date)"
