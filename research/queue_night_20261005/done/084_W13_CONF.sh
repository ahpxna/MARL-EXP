#!/usr/bin/env bash
# W13-2 / W13-3 (PROTOCOL_CITY_WAVE13_20261006): confirmation of the R13-F and R13-RB choices (from 083) on fresh grid4 traffic 900-919
# (generated after a non-existence check): R, TW8, TF, TRB, F1B x FRESH2 t14-t18 x s1013-s1313 x 20, under HBEFA4 and PHEMlight5 (same
# trajectories), modes wrapper on every row; report D13-1 / D13-2.  SMOKE=1: t14 x s1013, existing traffic 860, 600 s, into W13_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W13_DIR:-research/city_sim/w13_20261006}; F2=research/city_sim/w8_20261005/fresh2; G=research/city_sim/demand/grid4
RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P5=em:PHEMlight5/PC_EU4_G
mkdir -p $D/conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd); echo "W13-CONF start $(date)"
for f in choice_F.json choice_RB.json; do [ -f $D/tune/$f ] || { echo "missing $D/tune/$f (083 not done): stop"; exit 1; }; done
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="14"; FS="1013"; CS="860"; else SM=""; LT="14 15 16 17 18"; FS="1013 1113 1213 1313"; CS="$(seq -s ' ' 900 919)"; fi
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF900_generated ]; then
  for s in $(seq 900 919); do [ -f $G/rou_s$s.xml ] && { echo "KW13 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 900 919); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF900_generated; echo "traffic 900-919 generated $(date)"; fi
CH() { $PY -c "import json;c=json.load(open('$1'))['$2']['choice'].split(',');print(c[0]+':'+c[1]+' '+(c[2] if len(c)>2 else '0.5'))"; }
N4() { echo "--n4 $2:hyb:$F2/prep/prov_rlh$1_cl.json:$F2/cmodel/n2_k$1.pt"; }
J=$D/conf_jobs.txt; : > $J
for k in $LT; do read W8AB W8Q <<< "$(CH $F2/tune/choice.json $k)"; read FAB FQ <<< "$(CH $D/tune/choice_F.json $k)"; read RAB RQ <<< "$(CH $D/tune/choice_RB.json $k)"
  for s in $FS; do F="--light RL-H:$k --fleet PL:$F2/fleets/L11_s${s}_fleet.pt"; F1B=$(grep "^F1B_t${k}_s$s " $F2/conf_jobs.txt | cut -d' ' -f2-)
    [ -n "$F1B" ] || { echo "no F1B command t$k s$s"; exit 1; }
    for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
      echo "R${x}_t${k}_s$s $em scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
      echo "TW8${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $(N4 $k 0.5) $F --light-obs q:$W8AB" >> $J
      echo "TF${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $(N4 $k $FQ) $F --light-obs q:$FAB" >> $J
      echo "TRB${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $(N4 $k $RQ) $F --light-obs q:$RAB" >> $J
      echo "F1B${x}_t${k}_s$s $em $F1B" >> $J; done; done; done
export PY D SM; export SS="$CS"
xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $D/conf/$T.json ] || nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation failure: stop"; exit 1; }
if [ "${SMOKE:-0}" = 1 ]; then W13_SMOKE=1 W13_SEED=860 $PY scripts/CITY_w13_conf_report.py $D; else $PY scripts/CITY_w13_conf_report.py $D; fi || { echo "report FAIL"; exit 1; }
echo "W13-CONF done $(date)"
