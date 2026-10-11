#!/usr/bin/env bash
# W15-2 (PROTOCOL_CITY_WAVE15_20261007): state-dependent quantile (27 configurations at adapter (1, 0.25), q-column replaced through
# CITY_w15_qstate) x HBEFA4 / PHEMlight5 on FRESH2 TUNE 660-663 -> R15-U over these and the W13 grid -> fresh traffic 1060-1079 ->
# R, TRB, TU, TG, F1B x HBEFA4 / PHEMlight5 -> report D15-2a / D15-2b.  SMOKE=1: t14, TUNE 660, conf 860, 600 s, two configurations.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
B=${W15_DIR:-research/city_sim/w15_20261007}; D=$B/qstate; F2=research/city_sim/w8_20261005/fresh2; W13=research/city_sim/w13_20261006
DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt; G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py
P5=em:PHEMlight5/PC_EU4_G; mkdir -p $D/tune $D/conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd); echo "W15-QSTATE start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="14"; FS="1013"; TS="660"; CS="860"; QSL="-2:1:1 2:0:0"; else SM=""; LT="14 15 16 17 18"; FS="1013 1113 1213 1313"; TS="660 661 662 663"; CS="$(seq -s ' ' 1060 1079)"
  QSL=""; for a in -2 0 2; do for b in 0 1 3; do for c in 0 1 3; do QSL="$QSL $a:$b:$c"; done; done; done; fi
N4() { echo "--n4 $2:hyb:$F2/prep/prov_rlh$1_cl.json:$F2/cmodel/n2_k$1.pt"; }
enc() { case $1 in -*) echo "m${1#-}";; *) echo "$1";; esac; }
run_jobs() { export PY SM; export OUT=$2 SS="$3"
  xargs -P 6 -L 1 bash -c 'T=$0; M=$1; QS=$2; shift 2; [ -f $OUT/$T.json ] && exit 0; if [ "$QS" = "-" ]; then W=""; else W="scripts/CITY_w15_qstate.py"; export W15_QS=$QS; fi
    nice -n 5 $PY -u scripts/CITY_w9_run.py $M $W scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
J=$D/tune_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$DEV"
  [ "${SMOKE:-0}" = 1 ] && { echo "R_t${k} none - scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "R_t${k}_P5 $P5 - scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; }
  for qs in $QSL; do IFS=: read a b c <<< "$qs"; T="S_t${k}_a$(enc $a)_b$(enc $b)_c$(enc $c)"
    echo "$T none $qs scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:1:0.25" >> $J; echo "${T}_P5 $P5 $qs scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:1:0.25" >> $J; done; done
run_jobs $J $D/tune "$TS" || { echo "tuning failure: stop"; exit 1; }
W15_SMOKE=${SMOKE:-0} $PY scripts/CITY_w15_u.py select $D || { echo "selection FAIL: stop"; exit 1; }
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF1060_generated ]; then
  for s in $CS; do [ -f $G/rou_s$s.xml ] && { echo "KW15-2 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $CS; do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF1060_generated; echo "traffic 1060-1079 generated $(date)"; fi
J=$D/conf_jobs.txt; : > $J
for k in $LT; do RB=$($PY -c "import json;c=json.load(open('$W13/tune/choice_RB.json'))['$k']['choice'].split(',');print(c[0]+':'+c[1]+' '+c[2])"); read RAB RQ <<< "$RB"
  U=$($PY -c "
import json; c=json.load(open('$D/tune/choice_U.json'))['$k']['choice']; kind,_,v=c.partition(':')
print(('- '+v.split(',')[0]+':'+v.split(',')[1]+' '+v.split(',')[2]) if kind=='grid' else (v+' 1:0.25 0.1'))"); read UQS UAB UQ <<< "$U"
  for s in $FS; do F="--light RL-H:$k --fleet PL:$F2/fleets/L11_s${s}_fleet.pt"; F1B=$(grep "^F1B_t${k}_s$s " $F2/conf_jobs.txt | cut -d' ' -f2-)
    for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
      echo "R${x}_t${k}_s$s $em - scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
      echo "TRB${x}_t${k}_s$s $em - scripts/CITY_eval_n4.py $(N4 $k $RQ) $F --light-obs q:$RAB" >> $J
      echo "TU${x}_t${k}_s$s $em $UQS scripts/CITY_eval_n4.py $(N4 $k $UQ) $F --light-obs q:$UAB" >> $J
      echo "TG${x}_t${k}_s$s $em - scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:1:0.25" >> $J
      echo "F1B${x}_t${k}_s$s $em - $F1B" >> $J; done; done; done
run_jobs $J $D/conf "$CS" || { echo "confirmation failure: stop"; exit 1; }
W15_SMOKE=${SMOKE:-0} $PY scripts/CITY_w15_u.py report $D || { echo "report FAIL"; exit 1; }
echo "W15-QSTATE done $(date)"
