#!/usr/bin/env bash
# W9-1..W9-5 (PROTOCOL_CITY_WAVE9_20261005): robustness of the frozen TSI design on the W7-1 fresh-policy panel (lights t9-t13 x fleets
# s613-s913 x traffic 780-799; W7-1 providers and adapter choices unchanged) under SPaT latency / loss, adapter sensing errors, a second
# emission model and IDM; the global adapter (1, 0.5) on the W8-2 FRESH2 panel (registered decision) and on W7-1 t9/t11/t12 (secondary);
# the offline calibration-budget analysis; reports.  SMOKE=1: t9 x s613, seed 780, 600 s, into W9_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W9_DIR:-research/city_sim/w9_20261005/robust}; W7=research/city_sim/w7_20261005/fpr; F2=research/city_sim/w8_20261005/fresh2
mkdir -p $D/conf $D/glob $D/check; export XPLAY_TMP=$(cd $D/check && pwd); W9="$PY -u scripts/CITY_w9_run.py"; echo "W9-ROBUST start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="9"; FS="613"; CS="780"; else SM=""; LT="9 10 11 12 13"; FS="613 713 813 913"; CS="$(seq -s ' ' 780 799)"; fi
# W9-1 .. W9-4 on the W7-1 panel
J=$D/conf_jobs.txt; : > $J
for k in $LT; do AB=$($PY -c "import json;print(json.load(open('$W7/tune/choice.json'))['$k']['choice'].replace(',',':'))"); N4="--n4 0.5:hyb:$W7/prep/prov_rlh${k}_cl.json:$W7/cmodel/n2_k$k.pt"
  for s in $FS; do F="--light RL-H:$k --fleet PL:$W7/fleets/L11_s${s}_fleet.pt"; T="scripts/CITY_eval_n4.py $N4 $F --light-obs q:$AB"; R="scripts/CITY_eval_f1.py --spat-arm none $F"
    echo "TSI_LAT1_t${k}_s$s lat:1 $T" >> $J; echo "TSI_LOSS20_t${k}_s$s loss:0.2 $T" >> $J; echo "TSI_LOSS50_t${k}_s$s loss:0.5 $T" >> $J
    echo "TSI_DET80_t${k}_s$s det:0.8 $T" >> $J; echo "TSI_SPN1_t${k}_s$s spn:1 $T" >> $J
    echo "R_EM2_t${k}_s$s em:PHEMlight5/PC_EU4_G $R" >> $J; echo "TSI_EM2_t${k}_s$s em:PHEMlight5/PC_EU4_G $T" >> $J
    echo "R_IDM_t${k}_s$s idm $R" >> $J; echo "TSI_IDM_t${k}_s$s idm $T" >> $J; done; done
export PY D W9 SM; export SS="$CS"
xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $D/conf/$T.json ] || nice -n 5 $W9 $M "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "W9-1..4 failure: stop"; exit 1; }
echo "W9-1..4 panel done $(date)"
# W9-5 (b): global (1, 0.5) on W7-1 t9 / t11 / t12 (t10 / t13 equal their W7-1 choice: rows reused) + identity check KW9-5
J=$D/glob_jobs.txt; : > $J; GL="9 11 12"; [ "${SMOKE:-0}" = 1 ] && GL="9"
for k in $GL; do N4="--n4 0.5:hyb:$W7/prep/prov_rlh${k}_cl.json:$W7/cmodel/n2_k$k.pt"
  for s in $FS; do echo "TSIG_t${k}_s$s none scripts/CITY_eval_n4.py $N4 --light RL-H:$k --fleet PL:$W7/fleets/L11_s${s}_fleet.pt --light-obs q:1:0.5" >> $J; done; done
xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $D/glob/$T.json ] || nice -n 5 $W9 $M "$@" --seeds $SS $SM --tag $T --out $D/glob >> $D/glob/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "W9-5b failure: stop"; exit 1; }
if [ "${SMOKE:-0}" != 1 ]; then [ -f $D/check/KW95_t10_s613.json ] || $W9 none scripts/CITY_eval_n4.py --n4 0.5:hyb:$W7/prep/prov_rlh10_cl.json:$W7/cmodel/n2_k10.pt --light RL-H:10 \
  --fleet PL:$W7/fleets/L11_s613_fleet.pt --light-obs q:1:0.5 --seeds 780 --tag KW95_t10_s613 --out $D/check >> $D/check/run.log 2>&1 || { echo "KW9-5 run FAIL"; exit 1; }; fi
# W9-5 (a): global (1, 0.5) on the FRESH2 panel (only if FRESH2 completed)
if [ "${SMOKE:-0}" != 1 ]; then
  if [ -f $F2/report_fresh2.txt ]; then J=$D/glob2_jobs.txt; : > $J
    for k in 14 15 16 17 18; do N4="--n4 0.5:hyb:$F2/prep/prov_rlh${k}_cl.json:$F2/cmodel/n2_k$k.pt"
      for s in 1013 1113 1213 1313; do echo "TSIG_t${k}_s$s none scripts/CITY_eval_n4.py $N4 --light RL-H:$k --fleet PL:$F2/fleets/L11_s${s}_fleet.pt --light-obs q:1:0.5" >> $J; done; done
    export SS="$(seq -s ' ' 800 819)"
    xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $D/glob/$T.json ] || nice -n 5 $W9 $M "$@" --seeds $SS --tag $T --out $D/glob >> $D/glob/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "W9-5a failure: stop"; exit 1; }
  else echo "W9-5 (a) NOT RUN: FRESH2 did not complete (no report_fresh2.txt)"; fi
fi
echo "W9-5 panels done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W9_SMOKE=$(dirname $D) $PY scripts/CITY_w9_report.py robust; W9_SMOKE=$(dirname $D) $PY scripts/CITY_w9_report.py global
else $PY scripts/CITY_w9_report.py robust; $PY scripts/CITY_w9_report.py global; fi || exit 1
$PY scripts/CITY_w9_calbudget.py | tee $D/report_calbudget.txt || exit 1
echo "W9-ROBUST done $(date)"
