#!/usr/bin/env bash
cd /Users/phanan/cig-amf-main; D=research/city_sim/m4_20261004/spider; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 XPLAY_TMP=$PWD/$D/tmp; mkdir -p $D/tmp $D/dev
i=0; while [ $i -lt 120 ] && [ $(ls $D/RLK_sp11.pt $D/RLK_sp111.pt 2>/dev/null | wc -l) -lt 2 ]; do sleep 10; i=$((i+1)); done
PY=$PWD/external_envs/city_runtime/bin/python; export SUMO_HOME=$PWD/external_envs/city_runtime/lib/python3.12/site-packages/sumo; RT=$SUMO_HOME/tools/randomTrips.py
DD=research/city_sim/demand/spider/p2.0; for s in $(seq 100 109); do $PY $RT -n research/city_sim/net/spider.net.xml -o $DD/trips_s$s.xml -r $DD/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1; done
NET=research/city_sim/net/spider.net.xml; ROU="$DD/rou_s{}.xml"; S="100 101 102 103 104 105 106 107 108 109"
$PY -u scripts/CITY_m4g_eval.py --net $NET --rou "$ROU" --light FT --seeds $S --tag FT --out $D/dev > $D/dev/FT.out 2>&1 &
for sd in 11 111; do $PY -u scripts/CITY_m4g_eval.py --net $NET --rou "$ROU" --light RLK:$D/RLK_sp$sd.pt --seeds $S --tag RLK_sp$sd --out $D/dev > $D/dev/RLK_sp$sd.out 2>&1 & done; wait
$PY scripts/CITY_m4_stage1_report.py
