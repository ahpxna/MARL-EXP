#!/usr/bin/env bash
# R10 evaluation (Amendment R10).  pilot: SELECT (seeds 13, 113 + GLOSA-L∘σ* + comparators);  confirm: fresh 450-469, only if GATE_PASS.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/spat_pilot_20261004/fleets_v11; ST=$1
run() { E=$1; shift; mkdir -p $E/tmp; XPLAY_TMP=$PWD/$E/tmp nice -n 5 $PY -u "$@" --out $E >> $E/run.log 2>&1 || echo "FAIL $*"; }
if [ "$ST" = pilot ]; then E=$D/eval_select; S="100 101 102 103 104"; FL="13 113"
else [ -f $D/eval_select/GATE_PASS ] || { echo "R10 pilot gate not passed: confirmation not evaluated (registered)"; exit 0; }
  E=$D/eval_450; S="450 451 452 453 454 455 456 457 458 459 460 461 462 463 464 465 466 467 468 469"; FL="213 313 413 513"; fi
for f in $FL; do run $E scripts/CITY_eval6_v11.py --light FT --fleet PL:$D/L11_s${f}_fleet.pt --seeds $S --tag L11_s$f & done
run $E scripts/CITY_eval6_lane.py --light FT --fleet GLOSAL:0.3 --seeds $S --tag GLOSALS &
run $E scripts/CITY_eval4.py --light FT --fleet L-ACT:0 --guard always --seeds $S --tag OFF_FT &
for sg in 0.0 0.1 0.2 0.3 0.4; do run $E scripts/CITY_eval4_sigma.py --sigma $sg --light FT --fleet L-ACT:0 --guard always --seeds $S --tag S${sg}_FT & done
wait
$PY scripts/CITY_v11_report.py $ST
