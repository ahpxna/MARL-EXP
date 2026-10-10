#!/usr/bin/env bash
# W14-3 (PROTOCOL_CITY_WAVE14_20261007, Amendment A1): the W13 method on the original one-lane spider (RLK 11 / 111, rule fleet GLOSAL:0.3,
# attempt-1 N2K networks): tuning grid (11 adapter settings x q 0.1 / 0.5 x HBEFA4 / PHEMlight5; TUNE 1100-1103) -> R13-RB -> fresh spider
# traffic 1190-1209 (non-existence check) -> R, TOLD, TRB x HBEFA4 / PHEMlight5 -> D14-3 (alpha 0.003125).  Every run through
# CITY_w9_run <em> -> CITY_w14_q (W14_Q) -> CITY_w13_modes -> CITY_m4s_tsi_eval.  SMOKE=1: RLK 11, TUNE 1100, conf 1100, 600 s, into W14_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
B=${W14_DIR:-research/city_sim/w14_20261007}; D=$B/spider; SP=research/city_sim/m4_20261004/spider; ST=research/city_sim/sptsi_20261005
G=research/city_sim/demand/spider/p2.0; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P5=em:PHEMlight5/PC_EU4_G
mkdir -p $D/tune $D/conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd); echo "W14-SPIDER start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LK="11"; TS="1100"; CS="1100"; else SM=""; LK="11 111"; TS="1100 1101 1102 1103"; CS="$(seq -s ' ' 1190 1209)"; fi
GRID="0:0 1:0 2:0 1:0.25 1.5:0.25 1:0.5 2:0.5 1:0.75 2:0.75 1:1 2:1"
TK() { echo "--tk n2k:$SP/s3b/prov/fkcl_rlk$1.json:$ST/model/n2k_sp$1.pt"; }
J=$D/tune_jobs.txt; : > $J
for k in $LK; do L="RLK:$SP/RLK_sp$k.pt"; echo "R_${k}_P5 $P5 0.5 --tk none --light $L --fleet GLOSAL:0.3" >> $J
  [ "${SMOKE:-0}" = 1 ] && echo "R_${k} none 0.5 --tk none --light $L --fleet GLOSAL:0.3" >> $J
  for g in $GRID; do a=${g%%:*}; b=${g##*:}; T="T_${k}_a${a//./p}_b${b//./p}"; LQ="RLKQ:$SP/RLK_sp$k.pt:$a:$b"
    echo "${T}_P5 $P5 0.5 $(TK $k) --light $LQ --fleet GLOSAL:0.3" >> $J; echo "${T}_q01 none 0.1 $(TK $k) --light $LQ --fleet GLOSAL:0.3" >> $J
    echo "${T}_q01_P5 $P5 0.1 $(TK $k) --light $LQ --fleet GLOSAL:0.3" >> $J
    [ "${SMOKE:-0}" = 1 ] && echo "${T} none 0.5 $(TK $k) --light $LQ --fleet GLOSAL:0.3" >> $J; done; done
run() { export PY SM; export OUT=$2 SS="$3"
  xargs -P 6 -L 1 bash -c 'T=$0; M=$1; Q=$2; shift 2; [ -f $OUT/$T.json ] || W14_Q=$Q nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_w14_q.py scripts/CITY_w13_modes.py scripts/CITY_m4s_tsi_eval.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
run $J $D/tune "$TS" || { echo "tuning failure: stop"; exit 1; }
W14_SMOKE=${SMOKE:-0} $PY scripts/CITY_w14_spider.py select $D || { echo "selection FAIL: stop"; exit 1; }
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF1190_generated ]; then
  for s in $CS; do [ -f $G/rou_s$s.xml ] && { echo "KW14-3 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $CS; do $PY $RT -n research/city_sim/net/spider.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF1190_generated; echo "spider traffic 1190-1209 generated $(date)"; fi
CH() { $PY -c "import json;c=json.load(open('$1'))['$2']['choice'].split(',');print(c[0]+':'+c[1]+' '+(c[2] if len(c)>2 else '0.5'))"; }
J=$D/conf_jobs.txt; : > $J
for k in $LK; do read OAB OQ <<< "$(CH $ST/tune/choice.json $k)"; read RAB RQ <<< "$(CH $D/tune/choice_RB.json $k)"; L="RLK:$SP/RLK_sp$k.pt"
  for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
    echo "R${x}_$k $em 0.5 --tk none --light $L --fleet GLOSAL:0.3" >> $J
    echo "TOLD${x}_$k $em 0.5 $(TK $k) --light RLKQ:$SP/RLK_sp$k.pt:$OAB --fleet GLOSAL:0.3" >> $J
    echo "TRB${x}_$k $em $RQ $(TK $k) --light RLKQ:$SP/RLK_sp$k.pt:$RAB --fleet GLOSAL:0.3" >> $J; done; done
run $J $D/conf "$CS" || { echo "confirmation failure: stop"; exit 1; }
W14_SMOKE=${SMOKE:-0} $PY scripts/CITY_w14_spider.py report $D || { echo "report FAIL"; exit 1; }
echo "W14-SPIDER done $(date)"
