#!/usr/bin/env bash
# W15-4 (PROTOCOL_CITY_WAVE15_20261007, Amendment A1): projected-queue adapter (CITY_w15_pq, tau in {3, 5, 10, 15}) x q {0.1, 0.5} x
# HBEFA4 / PHEMlight5 on three networks; R13-RB per light; confirmation on fresh traffic: grid4 FRESH2 (1180-1199), one-lane spider
# (1210-1229, sixth attempt, alpha 0.0015625), rand3 (740-759).  The reference R never uses the adapter.  SMOKE=1: first light / fleet,
# one TUNE seed, conf 860 (grid4) / 1100 (spider) / 660 (rand3), 600 s, into W15_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
B=${W15_DIR:-research/city_sim/w15_20261007}/pq; F2=research/city_sim/w8_20261005/fresh2; W13=research/city_sim/w13_20261006; W14=research/city_sim/w14_20261007
SP=research/city_sim/m4_20261004/spider; ST=research/city_sim/sptsi_20261005; N=research/city_sim/w8_20261005/net3; N3B=research/city_sim/w10_20261005/n3b
DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P5=em:PHEMlight5/PC_EU4_G
echo "W15-PQ start $(date)"; [ "${SMOKE:-0}" = 1 ] && SM="--smoke" || SM=""
# lines: TAG EMMODE PQ(- or tau) Q(- or q, multi-green only) WRAP(- or n3) script args
run_jobs() { export PY SM; export OUT=$2 SS="$3"
  xargs -P 6 -L 1 bash -c 'T=$0; M=$1; PQ=$2; Q=$3; WR=$4; shift 4; [ -f $OUT/$T.json ] && exit 0; C=""
    [ "$WR" = n3 ] && C="$C scripts/CITY_n3_run.py"; [ "$PQ" != - ] && { C="$C scripts/CITY_w15_pq.py"; export W15_PQ=$PQ; }; [ "$Q" != - ] && { C="$C scripts/CITY_w14_q.py"; export W14_Q=$Q; }
    nice -n 5 $PY -u scripts/CITY_w9_run.py $M $C scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
gen() {  # net dir seeds period
  local G=research/city_sim/demand/$2; [ "${SMOKE:-0}" = 1 ] && return 0; [ -f $G/CONF${3%% *}_generated ] && return 0
  for s in $3; do [ -f $G/rou_s$s.xml ] && { echo "KW15-4 FAIL: $G/rou_s$s existed"; exit 1; }; done
  for s in $3; do $PY $RT -n research/city_sim/net/$1.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period $4 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF${3%% *}_generated; echo "traffic $2 ${3%% *}+ generated $(date)"; }
CH() { $PY -c "import json;c=json.load(open('$1'))['$2']['choice'].split(',');print(c[0]+':'+c[1]+' '+(c[2] if len(c)>2 else '0.5'))"; }
CP() { $PY -c "import json;c=json.load(open('$1'))['$2']['choice'].split(',');print(c[0]+' '+c[1])"; }
TAUS="3 5 10 15"; QL="0.1 0.5"; qt() { [ "$1" = 0.1 ] && echo 01 || echo 05; }
# ---------------- grid4 (FRESH2)
D=$B/grid4; mkdir -p $D/tune $D/conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd)
if [ "${SMOKE:-0}" = 1 ]; then LT="14"; FS="1013"; TS="660"; CS="860"; else LT="14 15 16 17 18"; FS="1013 1113 1213 1313"; TS="660 661 662 663"; CS="$(seq -s ' ' 1180 1199)"; fi
N4() { echo "--n4 $2:hyb:$F2/prep/prov_rlh$1_cl.json:$F2/cmodel/n2_k$1.pt"; }
J=$D/tune_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$DEV"; echo "R_t$k none - - - scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "R_t${k}_P5 $P5 - - - scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  for tau in $TAUS; do for q in $QL; do T="P_t${k}_tau${tau}_q$(qt $q)"; echo "$T none $tau - - scripts/CITY_eval_n4.py $(N4 $k $q) $F --light-obs q:0:0" >> $J; echo "${T}_P5 $P5 $tau - - scripts/CITY_eval_n4.py $(N4 $k $q) $F --light-obs q:0:0" >> $J; done; done; done
run_jobs $J $D/tune "$TS" || { echo "grid4 tuning failure: stop"; exit 1; }
W15_SMOKE=${SMOKE:-0} W15_TSEED=660 $PY scripts/CITY_w15_pq_eval.py select grid4 $D || { echo "grid4 selection FAIL"; exit 1; }
gen grid4 grid4 "$CS" 2.0
J=$D/conf_jobs.txt; : > $J
for k in $LT; do read RAB RQ <<< "$(CH $W13/tune/choice_RB.json $k)"; read PT PQ <<< "$(CP $D/tune/choice_P.json $k)"
  for s in $FS; do F="--light RL-H:$k --fleet PL:$F2/fleets/L11_s${s}_fleet.pt"
    for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
      echo "R${x}_t${k}_s$s $em - - - scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
      echo "TRB${x}_t${k}_s$s $em - - - scripts/CITY_eval_n4.py $(N4 $k $RQ) $F --light-obs q:$RAB" >> $J
      echo "TP${x}_t${k}_s$s $em $PT - - scripts/CITY_eval_n4.py $(N4 $k $PQ) $F --light-obs q:0:0" >> $J; done; done; done
run_jobs $J $D/conf "$CS" || { echo "grid4 confirmation failure: stop"; exit 1; }
W15_SMOKE=${SMOKE:-0} W15_SEED=860 $PY scripts/CITY_w15_pq_eval.py report grid4 $D || { echo "grid4 report FAIL"; exit 1; }
# ---------------- one-lane spider (sixth attempt)
D=$B/spider; mkdir -p $D/tune $D/conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd)
if [ "${SMOKE:-0}" = 1 ]; then LK="11"; TS="1100"; CS="1100"; else LK="11 111"; TS="1100 1101 1102 1103"; CS="$(seq -s ' ' 1210 1229)"; fi
TK() { echo "--tk n2k:$SP/s3b/prov/fkcl_rlk$1.json:$ST/model/n2k_sp$1.pt"; }
J=$D/tune_jobs.txt; : > $J
for k in $LK; do echo "R_$k none - - - scripts/CITY_m4s_tsi_eval.py --tk none --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J; echo "R_${k}_P5 $P5 - - - scripts/CITY_m4s_tsi_eval.py --tk none --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J
  for tau in $TAUS; do for q in $QL; do T="P_${k}_tau${tau}_q$(qt $q)"; for em in none $P5; do x=""; [ "$em" = none ] || x="_P5"
    echo "${T}$x $em $tau $q - scripts/CITY_m4s_tsi_eval.py $(TK $k) --light RLKQ:$SP/RLK_sp$k.pt:0:0 --fleet GLOSAL:0.3" >> $J; done; done; done; done
run_jobs $J $D/tune "$TS" || { echo "spider tuning failure: stop"; exit 1; }
W15_SMOKE=${SMOKE:-0} W15_TSEED=1100 $PY scripts/CITY_w15_pq_eval.py select spider $D || { echo "spider selection FAIL"; exit 1; }
gen spider spider/p2.0 "$CS" 2.0
J=$D/conf_jobs.txt; : > $J
for k in $LK; do read RAB RQ <<< "$(CH $W14/spider/tune/choice_RB.json $k)"; read PT PQ <<< "$(CP $D/tune/choice_P.json $k)"
  for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
    echo "R${x}_$k $em - - - scripts/CITY_m4s_tsi_eval.py --tk none --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J
    echo "TRB${x}_$k $em - $RQ - scripts/CITY_m4s_tsi_eval.py $(TK $k) --light RLKQ:$SP/RLK_sp$k.pt:$RAB --fleet GLOSAL:0.3" >> $J
    echo "TP${x}_$k $em $PT $PQ - scripts/CITY_m4s_tsi_eval.py $(TK $k) --light RLKQ:$SP/RLK_sp$k.pt:0:0 --fleet GLOSAL:0.3" >> $J; done; done
run_jobs $J $D/conf "$CS" || { echo "spider confirmation failure: stop"; exit 1; }
W15_SMOKE=${SMOKE:-0} W15_SEED=1100 $PY scripts/CITY_w15_pq_eval.py report spider $D || { echo "spider report FAIL"; exit 1; }
# ---------------- rand3
D=$B/rand3; mkdir -p $D/tune $D/conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd)
if [ "${SMOKE:-0}" = 1 ]; then LT="21"; FS="213"; TS="660"; CS="660"; else LT="21 22 23 24 25"; FS="213 313 413 513"; TS="660 661 662 663"; CS="$(seq -s ' ' 740 759)"; fi
N4R() { echo "--n4 $2:hyb:$N/prep/prov_rlh$1_cl.json:$N/cmodel/n2_k$1.pt"; }
J=$D/tune_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$N/fleets/N3_s13_fleet.pt"; echo "R_t$k none - - n3 scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "R_t${k}_P5 $P5 - - n3 scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  for tau in $TAUS; do for q in $QL; do T="P_t${k}_tau${tau}_q$(qt $q)"; echo "$T none $tau - n3 scripts/CITY_eval_n4.py $(N4R $k $q) $F --light-obs q:0:0" >> $J; echo "${T}_P5 $P5 $tau - n3 scripts/CITY_eval_n4.py $(N4R $k $q) $F --light-obs q:0:0" >> $J; done; done; done
run_jobs $J $D/tune "$TS" || { echo "rand3 tuning failure: stop"; exit 1; }
W15_SMOKE=${SMOKE:-0} W15_TSEED=660 $PY scripts/CITY_w15_pq_eval.py select rand3 $D || { echo "rand3 selection FAIL"; exit 1; }
gen rand3 rand3 "$CS" 5.0
J=$D/conf_jobs.txt; : > $J
for k in $LT; do read OAB OQ <<< "$(CH $N3B/tune/choice.json $k)"; read PT PQ <<< "$(CP $D/tune/choice_P.json $k)"
  for s in $FS; do F="--light RL-H:$k --fleet PL:$N/fleets/N3_s${s}_fleet.pt"
    for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
      echo "R${x}_t${k}_s$s $em - - n3 scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
      echo "TOLD${x}_t${k}_s$s $em - - n3 scripts/CITY_eval_n4.py $(N4R $k 0.5) $F --light-obs q:$OAB" >> $J
      echo "TP${x}_t${k}_s$s $em $PT - n3 scripts/CITY_eval_n4.py $(N4R $k $PQ) $F --light-obs q:0:0" >> $J; done; done; done
run_jobs $J $D/conf "$CS" || { echo "rand3 confirmation failure: stop"; exit 1; }
W15_SMOKE=${SMOKE:-0} W15_SEED=660 $PY scripts/CITY_w15_pq_eval.py report rand3 $D || { echo "rand3 report FAIL"; exit 1; }
echo "W15-PQ done $(date)"
