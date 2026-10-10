#!/usr/bin/env bash
# M4 stage 3 (Amendment M4-A5): checks KM4-3a..e on DEV seed 100, then fresh spider 1000-1019 (generated if absent; must not pre-exist), 11 jobs, report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; SP=research/city_sim/m4_20261004/spider; D=$SP/s3; RK=scripts/CITY_m4s_rlk.py
G=research/city_sim/demand/spider/p2.0; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py
run() { E=$1; shift; mkdir -p $E/tmp; XPLAY_TMP=$PWD/$E/tmp nice -n 5 $PY -u $RK "$@" --out $E >> $E/run.log 2>&1 || echo "FAIL $*"; }
L11=RLK:$SP/RLK_sp11.pt; L111=RLK:$SP/RLK_sp111.pt; F0="GLOSAL:0.3"; M=scripts/CITY_eval6_m2.py; SG=scripts/CITY_eval4_sigma.py
E=$D/check; echo "checks start $(date)"
run $E $M --spat-label labelled --light FT --fleet L-ACT:0 --guard always --seeds 100 --tag OFFm2_FT &
run $E $M --spat-label naive --light FT --fleet $F0 --seeds 100 --tag F0_FT_naive & run $E $M --spat-label labelled --light FT --fleet $F0 --seeds 100 --tag F0_FT_labelled &
run $E $M --spat-label labelled --light $L11 --fleet $F0 --seeds 100 --tag F0_RLK11_labelled & run $E $M --spat-label naive --light $L11 --fleet $F0 --seeds 100 --tag F0_RLK11_naive &
run $E $SG --sigma 0.3 --light $L11 --fleet L-ACT:0 --guard always --seeds 100 --tag S03_RLK11 & run $E $M --spat-label labelled --light $L11 --fleet L-ACT:0 --guard always --seeds 100 --tag OFFm2_RLK11 &
wait; $PY scripts/CITY_m4_s3_check.py || { echo "M4 stage 3 checks FAIL: stop"; exit 1; }
if [ ! -f $D/traffic_generated ]; then
  for s in $(seq 1000 1019); do [ -f $G/rou_s$s.xml ] && { echo "spider rou_s$s.xml existed before generation: stop"; exit 1; }; done
  for s in $(seq 1000 1019); do $PY $RT -n research/city_sim/net/spider.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger \
    --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; echo "generated $(date)" > $D/traffic_generated; fi
E=$D/eval; S="$(seq -s ' ' 1000 1019)"
run $E $M --spat-label labelled --light FT --fleet L-ACT:0 --guard always --seeds $S --tag OFF_FT & run $E $SG --sigma 0.3 --light FT --fleet L-ACT:0 --guard always --seeds $S --tag S03_FT &
run $E $M --spat-label naive --light FT --fleet $F0 --seeds $S --tag F0_FT &
for k in 11 111; do L=RLK:$SP/RLK_sp$k.pt
  run $E $M --spat-label labelled --light $L --fleet L-ACT:0 --guard always --seeds $S --tag OFF_RLK$k & run $E $SG --sigma 0.3 --light $L --fleet L-ACT:0 --guard always --seeds $S --tag S03_RLK$k &
  run $E $M --spat-label naive --light $L --fleet $F0 --seeds $S --tag F0_RLK${k}_naive & run $E $M --spat-label labelled --light $L --fleet $F0 --seeds $S --tag F0_RLK${k}_labelled &
done; wait; $PY scripts/CITY_m4_s3_report.py; echo "M4 stage 3 done $(date)"
