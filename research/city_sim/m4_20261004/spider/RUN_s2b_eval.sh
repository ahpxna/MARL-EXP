#!/usr/bin/env bash
# M4 2b evaluation (Amendment M4-A4).  pilot: DEV 100-109 (ESLD_s1 + comparators re-run in-dir);  confirm: fresh spider 1000-1019, only if GATE_PASS.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; SP=research/city_sim/m4_20261004/spider; D=$SP/s2b; ST=$1
run() { E=$1; shift; mkdir -p $E/tmp; XPLAY_TMP=$PWD/$E/tmp nice -n 5 $PY -u scripts/CITY_m4s_run.py "$@" --out $E >> $E/run.log 2>&1 || echo "FAIL $*"; }
if [ "$ST" = pilot ]; then E=$D/eval_dev; S="100 101 102 103 104 105 106 107 108 109"; FL="1"
else [ -f $D/eval_dev/GATE_PASS ] || { echo "M4 2b pilot gate not passed: confirmation not evaluated (registered)"; exit 0; }
  E=$D/eval_1000; S=""; for s in $(seq 1000 1019); do S="$S $s"
    [ -f research/city_sim/demand/spider/p2.0/rou_s$s.xml ] || $PY external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py -n research/city_sim/net/spider.net.xml \
      -o research/city_sim/demand/spider/p2.0/trips_s$s.xml -r research/city_sim/demand/spider/p2.0/rou_s$s.xml --prefix v --vehicle-class passenger \
      --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || echo "GEN FAIL $s"; done
  FL="2 3 4 5"; fi
for f in $FL; do run $E scripts/CITY_eval6_lane2.py --light FT --fleet ESLD:$D/theta_s$f.json --seeds $S --tag ESLD_s$f & done
run $E scripts/CITY_eval6_lane.py --light FT --fleet GLOSAL:0.3 --seeds $S --tag GLOSALS &
run $E scripts/CITY_eval4.py --light FT --fleet L-ACT:0 --guard always --seeds $S --tag OFF_FT &
for sg in 0.0 0.1 0.2 0.3 0.4; do run $E scripts/CITY_eval4_sigma.py --sigma $sg --light FT --fleet L-ACT:0 --guard always --seeds $S --tag S${sg}_FT & done
wait
$PY scripts/CITY_m4_s2b_report.py $ST; echo "M4 2b $ST done $(date)"
