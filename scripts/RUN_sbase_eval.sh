#!/usr/bin/env bash
# R7 evaluation (Amendment R7).  a: GLOSA∘σ* + comparators on SELECT and 420-429;  pilot: R7b search seed 1 on SELECT;
# confirm: R7b search seeds 2-5 on 420-429, only if sbase/eval_select/GATE_PASS.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/spat_pilot_20261004/sbase; ST=$1
run() { E=$1; shift; mkdir -p $E/tmp; XPLAY_TMP=$PWD/$E/tmp nice -n 5 $PY -u "$@" --out $E >> $E/run.log 2>&1 || echo "FAIL $*"; }
if [ "$ST" = a ]; then
  for pair in "eval_select:100 101 102 103 104" "eval_420:420 421 422 423 424 425 426 427 428 429"; do
    E=$D/${pair%%:*}; S=${pair#*:}
    run $E scripts/CITY_eval6_sbase.py --base-sigma 0.3 --light FT --fleet GLOSA --seeds $S --tag GLOSAS &
    run $E scripts/CITY_eval6.py --light FT --fleet GLOSA --seeds $S --tag GLOSA_FT &
    run $E scripts/CITY_eval4.py --light FT --fleet L-ACT:0 --guard always --seeds $S --tag OFF_FT &
    for sg in 0.0 0.1 0.2 0.3 0.4; do run $E scripts/CITY_eval4_sigma.py --sigma $sg --light FT --fleet L-ACT:0 --guard always --seeds $S --tag S${sg}_FT & done
  done; wait
elif [ "$ST" = pilot ]; then
  run $D/eval_select scripts/CITY_eval6_sbase.py --base-sigma 0.3 --light FT --fleet ES:$D/theta_s1.json --seeds 100 101 102 103 104 --tag ES_s1; wait
else
  [ -f $D/eval_select/GATE_PASS ] || { echo "R7b pilot gate not passed: confirmation not evaluated (registered)"; exit 0; }
  for f in 2 3 4 5; do run $D/eval_420 scripts/CITY_eval6_sbase.py --base-sigma 0.3 --light FT --fleet ES:$D/theta_s$f.json --seeds 420 421 422 423 424 425 426 427 428 429 --tag ES_s$f & done; wait
fi
$PY scripts/CITY_sbase_report.py $ST
