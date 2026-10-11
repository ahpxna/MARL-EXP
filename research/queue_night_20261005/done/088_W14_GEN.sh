#!/usr/bin/env bash
# W14-1 (PROTOCOL_CITY_WAVE14_20261007): the W13 method (per-light (A, B, q), rule R13-RB) on the two earlier grid4 panels.
#   TSI2: RL-H t4-t8 x fleets s213-s513 (F1-B arms available), providers f1b_20261004 / tsi_20261005; fresh traffic 980-999
#   W71 : RL-H t9-t13 x fleets s613-s913 (W7-1), providers w7_20261005/fpr;                              fresh traffic 1000-1019
# Per panel: tuning grid under PHEMlight5 and q 0.1 (TUNE 660-663, development fleet L11_s13) -> selection (KM13-1a) -> fresh traffic
# (non-existence check) -> R, TOLD (the panel's registered choice, q 0.5), TRB, TF [, F1B] x HBEFA4 / PHEMlight5 -> report D14-1 [, D14-2].
# SMOKE=1: first light / fleet, TUNE 660, conf seed 860, 600 s, into W14_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
B=${W14_DIR:-research/city_sim/w14_20261007}; DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt; G=research/city_sim/demand/grid4
RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P5=em:PHEMlight5/PC_EU4_G; echo "W14-GEN start $(date)"
GRID="1:0 1.5:0 2:0 1:0.25 1.5:0.25 2:0.25 1:0.5 1.5:0.5 2:0.5 3:0.5"
run_jobs() {  # $1 jobs file, $2 out dir, $3 seeds
  export PY SM; export OUT=$2 SS="$3"
  xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $OUT/$T.json ] || nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1
}
panel() {  # name lights fleets fleetdir provdir modeldir tune_old choice_old conf_from f1b(0/1)
  N=$1; LT=$2; FS=$3; FD=$4; PV=$5; MD=$6; TO=$7; CO=$8; C0=$9; F1=${10}; D=$B/$N; mkdir -p $D/tune $D/conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd)
  if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT=$(echo $LT | cut -d' ' -f1); FS=$(echo $FS | cut -d' ' -f1); TS="660"; CS="860"; else SM=""; TS="660 661 662 663"; CS="$(seq -s ' ' $C0 $((C0 + 19)))"; fi
  N4() { echo "--n4 $2:hyb:$PV/prov_rlh$1_cl.json:$MD/n2_k$1.pt"; }
  $PY -c "import json; json.dump(dict(name='$N', dir='$D', lights=[int(x) for x in '$LT'.split()], fleets=['s'+x for x in '$FS'.split()], tune_old='$TO',
    choice_old='$CO', tune_seeds=[int(x) for x in '$TS'.split()], conf_seeds=[int(x) for x in '$CS'.split()], f1b=bool($F1)), open('$D/panel.json','w'), indent=1)"
  J=$D/tune_jobs.txt; : > $J
  for k in $LT; do F="--light RL-H:$k --fleet PL:$DEV"; echo "R_t${k}_P5 $P5 scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
    [ "${SMOKE:-0}" = 1 ] && echo "R_t${k} none scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
    for g in $GRID; do a=${g%%:*}; b=${g##*:}; T="T_t${k}_a${a//./p}_b${b//./p}"
      echo "${T}_P5 $P5 scripts/CITY_eval_n4.py $(N4 $k 0.5) $F --light-obs q:$a:$b" >> $J; echo "${T}_q01 none scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:$a:$b" >> $J
      echo "${T}_q01_P5 $P5 scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:$a:$b" >> $J
      [ "${SMOKE:-0}" = 1 ] && echo "${T} none scripts/CITY_eval_n4.py $(N4 $k 0.5) $F --light-obs q:$a:$b" >> $J; done; done
  run_jobs $J $D/tune "$TS" || { echo "$N tuning failure: stop"; exit 1; }
  W14_SMOKE=${SMOKE:-0} $PY scripts/CITY_w14_gen.py select $D/panel.json || { echo "$N selection FAIL: stop"; exit 1; }
  if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF${C0}_generated ]; then
    for s in $CS; do [ -f $G/rou_s$s.xml ] && { echo "KW14 FAIL: rou_s$s existed"; exit 1; }; done
    for s in $CS; do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
    date > $G/CONF${C0}_generated; echo "traffic $C0+ generated $(date)"; fi
  CH() { $PY -c "import json;c=json.load(open('$1'))['$2']['choice'].split(',');print(c[0]+':'+c[1]+' '+(c[2] if len(c)>2 else '0.5'))"; }
  J=$D/conf_jobs.txt; : > $J
  for k in $LT; do read OAB OQ <<< "$(CH $CO $k)"; read FAB FQ <<< "$(CH $D/tune/choice_F.json $k)"; read RAB RQ <<< "$(CH $D/tune/choice_RB.json $k)"
    for s in $FS; do F="--light RL-H:$k --fleet PL:$FD/L11_s${s}_fleet.pt"
      F1B=""; [ "$F1" = 1 ] && { F1B=$(grep "^F1B_t${k}_F1B_s${s}_" research/city_sim/tsi2_20261005/conf_jobs.txt | cut -d' ' -f2-); [ -n "$F1B" ] || { echo "no F1B t$k s$s"; exit 1; }; }
      for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
        echo "R${x}_t${k}_s$s $em scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
        echo "TOLD${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $(N4 $k 0.5) $F --light-obs q:$OAB" >> $J
        echo "TRB${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $(N4 $k $RQ) $F --light-obs q:$RAB" >> $J
        echo "TF${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $(N4 $k $FQ) $F --light-obs q:$FAB" >> $J
        [ "$F1" = 1 ] && echo "F1B${x}_t${k}_s$s $em $F1B" >> $J; done; done; done
  run_jobs $J $D/conf "$CS" || { echo "$N confirmation failure: stop"; exit 1; }
  W14_SMOKE=${SMOKE:-0} $PY scripts/CITY_w14_gen.py report $D/panel.json || { echo "$N report FAIL"; exit 1; }
  echo "panel $N done $(date)"
}
SP=research/city_sim/spat_pilot_20261004/fleets_v11; W7=research/city_sim/w7_20261005/fpr
panel TSI2 "4 5 6 7 8" "213 313 413 513" $SP research/city_sim/f1b_20261004/prep research/city_sim/tsi_20261005/cmodel/c2 research/city_sim/tsi2_20261005/tune research/city_sim/tsi2_20261005/tune/choice.json 980 1
panel W71 "9 10 11 12 13" "613 713 813 913" $W7/fleets $W7/prep $W7/cmodel $W7/tune $W7/tune/choice.json 1000 0
echo "W14-GEN done $(date)"
