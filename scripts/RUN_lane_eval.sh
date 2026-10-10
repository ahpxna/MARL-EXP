#!/usr/bin/env bash
# R8 evaluation (Amendment R8).  dev: GLOSA-L∘σ* on the development teleport seeds;  confirm: fresh traffic 430-449, all comparators.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/spat_pilot_20261004/lane; ST=$1
run() { E=$1; shift; mkdir -p $E/tmp; XPLAY_TMP=$PWD/$E/tmp nice -n 5 $PY -u "$@" --out $E >> $E/run.log 2>&1 || echo "FAIL $*"; }
if [ "$ST" = dev ]; then
  run $D/eval_dev scripts/CITY_eval6_lane.py --light FT --fleet GLOSAL:0.3 --seeds 100 420 424 425 426 --tag GLOSALS
else
  E=$D/eval_430; S="430 431 432 433 434 435 436 437 438 439 440 441 442 443 444 445 446 447 448 449"
  run $E scripts/CITY_eval6_lane.py --light FT --fleet GLOSAL:0.3 --seeds $S --tag GLOSALS &
  run $E scripts/CITY_eval6_lane.py --light FT --fleet GLOSAL:0.5 --seeds $S --tag GLOSAL_FT &
  run $E scripts/CITY_eval6_sbase.py --base-sigma 0.3 --light FT --fleet GLOSA --seeds $S --tag GLOSAS &
  run $E scripts/CITY_eval6.py --light FT --fleet GLOSA --seeds $S --tag GLOSA_FT &
  run $E scripts/CITY_eval4.py --light FT --fleet L-ACT:0 --guard always --seeds $S --tag OFF_FT &
  for sg in 0.0 0.1 0.2 0.3 0.4; do run $E scripts/CITY_eval4_sigma.py --sigma $sg --light FT --fleet L-ACT:0 --guard always --seeds $S --tag S${sg}_FT & done
  wait
fi
$PY scripts/CITY_lane_report.py $ST
