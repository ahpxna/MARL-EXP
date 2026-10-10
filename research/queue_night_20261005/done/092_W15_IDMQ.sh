#!/usr/bin/env bash
# W15-3a (PROTOCOL_CITY_WAVE15_20261007): the quantile revision under IDM.  W13-6a IDM-recalibrated tables / networks (w13_20261006/idm);
# tuning grid C x q {0.1, 0.5} under IDM, HBEFA4 / PHEMlight5 (q 0.5 HBEFA4 rows reused from w13/idm/tune), TUNE 660-663 -> R13-RB / R13-F
# (CITY_w14_gen) -> fresh traffic 1080-1099 (every vehicle IDM) -> R, TOLD (W13-6a choice), TRB, TF, F1B x HBEFA4 / PHEMlight5 -> report
# (D14-1 of CITY_w14_gen = D15-3a; D14-2 = descriptive here).  All runs through CITY_w13_idm (W13_EM for PHEMlight5) + CITY_w13_modes.
# SMOKE=1: t14 x s1013, TUNE 660, conf 860, 600 s, into W15_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
B=${W15_DIR:-research/city_sim/w15_20261007}; D=$B/idmq; I=research/city_sim/w13_20261006/idm; F2=research/city_sim/w8_20261005/fresh2
DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt; G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py
mkdir -p $D/tune $D/conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd); echo "W15-IDMQ start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="14"; FS="1013"; TS="660"; CS="860"; else SM=""; LT="14 15 16 17 18"; FS="1013 1113 1213 1313"; TS="660 661 662 663"; CS="$(seq -s ' ' 1080 1099)"; fi
GRID="1:0 1.5:0 2:0 1:0.25 1.5:0.25 2:0.25 1:0.5 1.5:0.5 2:0.5 3:0.5"; N4() { echo "--n4 $2:hyb:$I/prep/prov_rlh$1_cl.json:$I/cmodel/n2_k$1.pt"; }
run_jobs() { export PY SM; export OUT=$2 SS="$3"
  xargs -P 6 -L 1 bash -c 'T=$0; X=$1; shift; [ -f $OUT/$T.json ] && exit 0; if [ "$X" = P5 ]; then export W13_EM=PHEMlight5/PC_EU4_G; fi; nice -n 5 $PY -u scripts/CITY_w13_idm.py scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
J=$D/tune_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$DEV"; echo "R_t${k}_P5 P5 scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  [ "${SMOKE:-0}" = 1 ] && echo "R_t${k} H4 scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  for g in $GRID; do a=${g%%:*}; b=${g##*:}; T="T_t${k}_a${a//./p}_b${b//./p}"
    echo "${T}_P5 P5 scripts/CITY_eval_n4.py $(N4 $k 0.5) $F --light-obs q:$a:$b" >> $J; echo "${T}_q01 H4 scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:$a:$b" >> $J
    echo "${T}_q01_P5 P5 scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:$a:$b" >> $J
    [ "${SMOKE:-0}" = 1 ] && echo "${T} H4 scripts/CITY_eval_n4.py $(N4 $k 0.5) $F --light-obs q:$a:$b" >> $J; done; done
run_jobs $J $D/tune "$TS" || { echo "tuning failure: stop"; exit 1; }
TO=$I/tune; [ "${SMOKE:-0}" = 1 ] && TO=$D/tune
$PY -c "import json; json.dump(dict(name='IDM', dir='$D', lights=[int(x) for x in '$LT'.split()], fleets=['s'+x for x in '$FS'.split()], tune_old='$TO', choice_old='$I/tune/choice.json', tune_seeds=[int(x) for x in '$TS'.split()], conf_seeds=[int(x) for x in '$CS'.split()], f1b=True), open('$D/panel.json','w'), indent=1)"
W14_SMOKE=0 $PY scripts/CITY_w14_gen.py select $D/panel.json || { echo "selection FAIL: stop"; exit 1; }
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF1080_generated ]; then
  for s in $CS; do [ -f $G/rou_s$s.xml ] && { echo "KW15-3 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $CS; do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF1080_generated; echo "traffic 1080-1099 generated $(date)"; fi
CH() { $PY -c "import json;c=json.load(open('$1'))['$2']['choice'].split(',');print(c[0]+':'+c[1]+' '+(c[2] if len(c)>2 else '0.5'))"; }
J=$D/conf_jobs.txt; : > $J
for k in $LT; do read OAB OQ <<< "$(CH $I/tune/choice.json $k)"; read FAB FQ <<< "$(CH $D/tune/choice_F.json $k)"; read RAB RQ <<< "$(CH $D/tune/choice_RB.json $k)"
  for s in $FS; do F="--light RL-H:$k --fleet PL:$F2/fleets/L11_s${s}_fleet.pt"; F1B=$(grep "^F1B_t${k}_s$s " $F2/conf_jobs.txt | cut -d' ' -f2-)
    for X in H4 P5; do x=""; [ "$X" = P5 ] && x=P5
      echo "R${x}_t${k}_s$s $X scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
      echo "TOLD${x}_t${k}_s$s $X scripts/CITY_eval_n4.py $(N4 $k 0.5) $F --light-obs q:$OAB" >> $J
      echo "TRB${x}_t${k}_s$s $X scripts/CITY_eval_n4.py $(N4 $k $RQ) $F --light-obs q:$RAB" >> $J
      echo "TF${x}_t${k}_s$s $X scripts/CITY_eval_n4.py $(N4 $k $FQ) $F --light-obs q:$FAB" >> $J
      echo "F1B${x}_t${k}_s$s $X $F1B" >> $J; done; done; done
run_jobs $J $D/conf "$CS" || { echo "confirmation failure: stop"; exit 1; }
W14_SMOKE=${SMOKE:-0} $PY scripts/CITY_w14_gen.py report $D/panel.json || { echo "report FAIL"; exit 1; }
echo "W15-IDMQ done $(date)"
