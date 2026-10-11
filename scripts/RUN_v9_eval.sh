#!/usr/bin/env bash
# v9 evaluation (Amendment R4): STAGE=pilot (SELECT, seeds 13 / 113) or confirm (420-429, seeds 213-513, only if GATE_PASS).
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=research/city_sim/spat_pilot_20261004; O=$D/fleets_v9; ST=$1
if [ "$ST" = pilot ]; then E=$D/v9_select; S="100 101 102 103 104"; F="13 113"
else [ -f $D/v9_select/GATE_PASS ] || { echo "v9 pilot gate not passed: confirmation not evaluated (registered)"; exit 0; }; E=$D/v9_confirm; S="420 421 422 423 424 425 426 427 428 429"; F="213 313 413 513"; fi
mkdir -p $E/tmp; export XPLAY_TMP=$PWD/$E/tmp
run() { nice -n 5 $PY -u "$@" --out $E >> $E/run.log 2>&1 || echo "FAIL $*"; }
for f in $F; do run scripts/CITY_eval6.py --light FT --fleet R:$O/R9_s${f}_fleet.pt --seeds $S --tag R9_s$f & done
run scripts/CITY_eval6.py --light FT --fleet IC:GLOSA --seeds $S --tag IC_FT &
run scripts/CITY_eval4.py --light FT --fleet L-ACT:0 --guard always --seeds $S --tag OFF_FT &
wait
for sg in 0.0 0.1 0.2 0.3 0.4; do run scripts/CITY_eval4_sigma.py --sigma $sg --light FT --fleet L-ACT:0 --guard always --seeds $S --tag S${sg}_FT & done
wait
$PY scripts/CITY_v9_report.py $ST
