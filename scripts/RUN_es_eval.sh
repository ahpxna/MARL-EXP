#!/usr/bin/env bash
# R6 evaluation: pilot (SELECT; search seed 1) or confirm (420-429; search seeds 2-5; only if GATE_PASS).
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/spat_pilot_20261004/es; ST=$1
if [ "$ST" = pilot ]; then E=$D/eval_select; S="100 101 102 103 104"; F="1"
else [ -f $D/eval_select/GATE_PASS ] || { echo "R6 pilot gate not passed: confirmation not evaluated (registered)"; exit 0; }; E=$D/eval_confirm; S="420 421 422 423 424 425 426 427 428 429"; F="2 3 4 5"; fi
mkdir -p $E/tmp; export XPLAY_TMP=$PWD/$E/tmp
run() { nice -n 5 $PY -u "$@" --out $E >> $E/run.log 2>&1 || echo "FAIL $*"; }
for f in $F; do run scripts/CITY_eval6.py --light FT --fleet ES:$D/theta_s$f.json --seeds $S --tag ES_s$f & done
run scripts/CITY_eval6.py --light FT --fleet GLOSA --seeds $S --tag GLOSA_FT &
run scripts/CITY_eval4.py --light FT --fleet L-ACT:0 --guard always --seeds $S --tag OFF_FT &
wait
for sg in 0.0 0.1 0.2 0.3 0.4; do run scripts/CITY_eval4_sigma.py --sigma $sg --light FT --fleet L-ACT:0 --guard always --seeds $S --tag S${sg}_FT & done
wait
$PY scripts/CITY_es_report.py $ST
