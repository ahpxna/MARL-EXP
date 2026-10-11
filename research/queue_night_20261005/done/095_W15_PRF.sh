#!/usr/bin/env bash
# W15-6 (PROTOCOL_CITY_WAVE15_20261007, Amendment A2): policy-aware forecaster (CITY_w15_prf, arrival model on) at adapter (1, 0.25), wrapped
# N4 hybrid at q 0.1; variants prf / prfq x HBEFA4 / PHEMlight5 on FRESH2 TUNE 660-663 -> R13-RB over {prf, prfq, tg} -> fresh traffic
# 1260-1279 -> R, TG, TPRF x HBEFA4 / PHEMlight5 -> report D15-6.  SMOKE=1: t14, TUNE 660, conf 860, 600 s, into W15_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W15_DIR:-research/city_sim/w15_20261007}/prf; F2=research/city_sim/w8_20261005/fresh2; DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P5=em:PHEMlight5/PC_EU4_G
mkdir -p $D/tune $D/conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd); echo "W15-PRF start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="14"; FS="1013"; TS="660"; CS="860"; else SM=""; LT="14 15 16 17 18"; FS="1013 1113 1213 1313"; TS="660 661 662 663"; CS="$(seq -s ' ' 1260 1279)"; fi
N4() { echo "--n4 0.1:hyb:$F2/prep/prov_rlh$1_cl.json:$F2/cmodel/n2_k$1.pt"; }
# lines: TAG EMMODE VARIANT(- | prf | prfq) LIGHT script args
run_jobs() { export PY SM; export OUT=$2 SS="$3"
  xargs -P 6 -L 1 bash -c 'T=$0; M=$1; V=$2; LS=$3; shift 3; [ -f $OUT/$T.json ] && exit 0; C=""; [ "$V" != - ] && { C="scripts/CITY_w15_prf.py"; export W15_PRF=1:0.25:$V W15_PRF_LIGHT=$LS; }
    nice -n 5 $PY -u scripts/CITY_w9_run.py $M $C scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
J=$D/tune_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$DEV"
  if [ "${SMOKE:-0}" = 1 ]; then for em in none $P5; do x=""; [ "$em" = none ] || x="_P5"; echo "R_t${k}$x $em - - scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
    echo "T_t${k}_a1_b0p25_q01$x $em - - scripts/CITY_eval_n4.py $(N4 $k) $F --light-obs q:1:0.25" >> $J; done; fi
  for v in prf prfq; do for em in none $P5; do x=""; [ "$em" = none ] || x="_P5"; echo "F_t${k}_${v}$x $em $v RL-H:$k scripts/CITY_eval_n4.py $(N4 $k) $F --light-obs q:1:0.25" >> $J; done; done; done
run_jobs $J $D/tune "$TS" || { echo "tuning failure: stop"; exit 1; }
W15_SMOKE=${SMOKE:-0} $PY scripts/CITY_w15_prf_eval.py select $D || { echo "selection FAIL: stop"; exit 1; }
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF1260_generated ]; then
  for s in $CS; do [ -f $G/rou_s$s.xml ] && { echo "KW15-6 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $CS; do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF1260_generated; echo "traffic 1260-1279 generated $(date)"; fi
J=$D/conf_jobs.txt; : > $J
for k in $LT; do V=$($PY -c "import json;print(json.load(open('$D/tune/choice_PRF.json'))['$k']['choice'])"); [ "$V" = tg ] && V=-
  for s in $FS; do F="--light RL-H:$k --fleet PL:$F2/fleets/L11_s${s}_fleet.pt"
    for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
      echo "R${x}_t${k}_s$s $em - - scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
      echo "TG${x}_t${k}_s$s $em - - scripts/CITY_eval_n4.py $(N4 $k) $F --light-obs q:1:0.25" >> $J
      echo "TPRF${x}_t${k}_s$s $em $V RL-H:$k scripts/CITY_eval_n4.py $(N4 $k) $F --light-obs q:1:0.25" >> $J; done; done; done
run_jobs $J $D/conf "$CS" || { echo "confirmation failure: stop"; exit 1; }
W15_SMOKE=${SMOKE:-0} $PY scripts/CITY_w15_prf_eval.py report $D || { echo "report FAIL"; exit 1; }
echo "W15-PRF done $(date)"
