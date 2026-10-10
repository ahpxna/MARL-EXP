#!/usr/bin/env bash
# W13-1 (PROTOCOL_CITY_WAVE13_20261006): (a) FRESH2 tuning grid under PHEMlight5 and at q = 0.1 (TUNE 660-663, development fleet L11_s13);
# (b) fuel-by-mode decomposition (R, HYB, TSI, F1B x t14-t18 x s1013 x 800-803; FT contrast s1013 x 820-823; HBEFA4 and PHEMlight5);
# selection (R13-F, R13-RB; KM13-1a) and the diagnosis report (KM13-1b, KM13-1c, registered reading).
# SMOKE=1: t14, TUNE 660, diag 800 / 820, 600 s, into W13_DIR (the q = 0.5 HBEFA4 tuning twins are produced there too).
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W13_DIR:-research/city_sim/w13_20261006}; F2=research/city_sim/w8_20261005/fresh2; DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt
mkdir -p $D/tune $D/diag $D/check; export XPLAY_TMP=$(cd $D/check && pwd); P5=em:PHEMlight5/PC_EU4_G; echo "W13-DIAG start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="14"; TS="660"; DS="800"; FT="820"; else SM=""; LT="14 15 16 17 18"; TS="660 661 662 663"; DS="800 801 802 803"; FT="820 821 822 823"; fi
GRID="1:0 1.5:0 2:0 1:0.25 1.5:0.25 2:0.25 1:0.5 1.5:0.5 2:0.5 3:0.5"
N4() { echo "--n4 $2:hyb:$F2/prep/prov_rlh$1_cl.json:$F2/cmodel/n2_k$1.pt"; }
# (a) tuning grid
J=$D/tune_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$DEV"
  echo "R_t${k}_P5 $P5 scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  [ "${SMOKE:-0}" = 1 ] && echo "R_t${k} none scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  for g in $GRID; do a=${g%%:*}; b=${g##*:}; T="T_t${k}_a${a//./p}_b${b//./p}"
    echo "${T}_P5 $P5 scripts/CITY_eval_n4.py $(N4 $k 0.5) $F --light-obs q:$a:$b" >> $J
    echo "${T}_q01 none scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:$a:$b" >> $J
    echo "${T}_q01_P5 $P5 scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:$a:$b" >> $J
    [ "${SMOKE:-0}" = 1 ] && echo "${T} none scripts/CITY_eval_n4.py $(N4 $k 0.5) $F --light-obs q:$a:$b" >> $J; done; done
export PY D SM; export SS="$TS"
xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $D/tune/$T.json ] || nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $D/tune >> $D/tune/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "tuning failure: stop"; exit 1; }
echo "tuning grid done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W13_SMOKE=1 $PY scripts/CITY_w13_select.py $D; else $PY scripts/CITY_w13_select.py $D; fi || { echo "selection / KM13-1a FAIL: stop"; exit 1; }
# (b) decomposition
J=$D/diag_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$F2/fleets/L11_s1013_fleet.pt"
  AB=$($PY -c "import json;print(json.load(open('$F2/tune/choice.json'))['$k']['choice'].replace(',',':'))" 2>/dev/null || echo "1:0.5")
  F1B=$(grep "^F1B_t${k}_s1013 " $F2/conf_jobs.txt | cut -d' ' -f2-)
  [ -n "$F1B" ] || { echo "no F1B command for t$k"; exit 1; }
  for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
    echo "DR${x}_t${k}_s1013 $em scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
    echo "DHYB${x}_t${k}_s1013 $em scripts/CITY_eval_n4.py $(N4 $k 0.5) $F" >> $J
    echo "DTSI${x}_t${k}_s1013 $em scripts/CITY_eval_n4.py $(N4 $k 0.5) $F --light-obs q:$AB" >> $J
    echo "DF1B${x}_t${k}_s1013 $em $F1B" >> $J; done; done
export SS="$DS"
xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $D/diag/$T.json ] || nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $D/diag >> $D/diag/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "diag failure: stop"; exit 1; }
J=$D/diagft_jobs.txt; : > $J; P="PL:$F2/fleets/L11_s1013_fleet.pt"
for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
  echo "DRFT${x}_s1013 $em scripts/CITY_eval_f1.py --spat-arm none --light FT --fleet $P" >> $J
  echo "DPLFT${x}_s1013 $em scripts/CITY_eval6_v11.py --light FT --fleet $P" >> $J; done
export SS="$FT"
xargs -P 4 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $D/diag/$T.json ] || nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $D/diag >> $D/diag/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "diag FT failure: stop"; exit 1; }
if [ "${SMOKE:-0}" = 1 ]; then W13_SMOKE=1 $PY scripts/CITY_w13_diag_report.py $D; else $PY scripts/CITY_w13_diag_report.py $D; fi || { echo "diag report FAIL"; exit 1; }
echo "W13-DIAG done $(date)"
