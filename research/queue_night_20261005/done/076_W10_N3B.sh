#!/usr/bin/env bash
# W10-6 rand3 attempt 2 (PROTOCOL_CITY_WAVE10_20261005, A3): extended adapter grid on TUNE 660-663 (NET3 lights t21-t25, dev fleet N3_s13,
# NET3 providers) -> choice -> fresh rand3 720-739 -> R / TSIX x t21-t25 x s213-s513 -> report (alpha 0.025).  SMOKE=1: t21 x s213, 600 s.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W10_DIR:-research/city_sim/w10_20261005/n3b}; N=research/city_sim/w8_20261005/net3; mkdir -p $D/tune $D/conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd)
G=research/city_sim/demand/rand3; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; RUN="$PY -u scripts/CITY_n3_run.py"
export W10_GRID="2:0.5,3:0.5,4:0.5,6:0.5,2:1,3:1,4:1,6:1,2:2,3:2,4:2,6:2"; echo "W10-N3B start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="21"; FS="213"; TUNES="660"; CS="660"; export W10_TUNE_SEEDS=660; else SM=""; LT="21 22 23 24 25"; FS="213 313 413 513"; TUNES="660 661 662 663"; CS="$(seq -s ' ' 720 739)"; fi
DEV=$N/fleets/N3_s13_fleet.pt; J=$D/tune_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$DEV"; echo "R_t$k scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  for ab in $(echo $W10_GRID | tr ',' ' '); do a=${ab%%:*}; b=${ab##*:}; T=$(echo "T_t${k}_a${a}_b${b}" | tr '.' 'p')
    echo "$T scripts/CITY_eval_n4.py --n4 0.5:hyb:$N/prep/prov_rlh${k}_cl.json:$N/cmodel/n2_k$k.pt $F --light-obs q:$a:$b" >> $J; done; done
export PY D RUN SM SS="$TUNES"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/tune/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/tune >> $D/tune/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "tuning failed: stop"; exit 1; }
$PY scripts/CITY_w10_tune_grid.py $D $LT | tee $D/tune/tune.txt || { echo "TUNE FAIL"; exit 1; }
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF720_generated ]; then for s in $(seq 720 739); do [ -f $G/rou_s$s.xml ] && { echo "KW10-6 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 720 739); do $PY $RT -n research/city_sim/net/rand3.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 5.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; date > $G/CONF720_generated; fi
J=$D/conf_jobs.txt; : > $J
for k in $LT; do AB=$($PY -c "import json;print(json.load(open('$D/tune/choice.json'))['$k']['choice'].replace(',',':'))"); N4="--n4 0.5:hyb:$N/prep/prov_rlh${k}_cl.json:$N/cmodel/n2_k$k.pt"
  for s in $FS; do F="--light RL-H:$k --fleet PL:$N/fleets/N3_s${s}_fleet.pt"; echo "R_t${k}_s$s scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "TSIX_t${k}_s$s scripts/CITY_eval_n4.py $N4 $F --light-obs q:$AB" >> $J; done; done
export SS="$CS"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation failed: stop"; exit 1; }
echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W10_SMOKE=$(dirname $D) W10_SEED=660 $PY scripts/CITY_w10_report2.py n3b; else $PY scripts/CITY_w10_report2.py n3b; fi || exit 1; echo "W10-N3B done $(date)"
