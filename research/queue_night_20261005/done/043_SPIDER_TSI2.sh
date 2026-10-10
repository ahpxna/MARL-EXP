#!/usr/bin/env bash
# SPIDER-TSI-2 (PROTOCOL_CITY_SPIDER_TSI_20261005 Amendment A2): wider adapter grid on TUNE 1100-1103 -> choice -> fresh 1130-1149 confirmation -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/sptsi_20261005; export XPLAY_TMP=$PWD/$D/check
SP=research/city_sim/m4_20261004/spider; G=research/city_sim/demand/spider/p2.0; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; EV="$PY -u scripts/CITY_m4s_tsi_eval.py"; echo "SPTSI2 start $(date)"
if [ ! -f $G/CONF1130_generated ]; then for s in $(seq 1130 1149); do [ -f $G/rou_s$s.xml ] && { echo "KS-0 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 1130 1149); do $PY $RT -n research/city_sim/net/spider.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; date > $G/CONF1130_generated; fi
J=$D/tune2_jobs.txt; : > $J
for k in 11 111; do TK="n2k:$SP/s3b/prov/fkcl_rlk$k.json:$D/model/n2k_sp$k.pt"
  for ab in "1 0.75" "2 0.75" "1 1.0" "2 1.0"; do set -- $ab; T=$(echo "T_${k}_a$1_b$2" | tr '.' 'p'); T=${T/b1p0/b1}; echo "$T --tk $TK --light RLKQ:$SP/RLK_sp$k.pt:$1:$2 --fleet GLOSAL:0.3" >> $J; done; done
export PY D EV; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/tune2/$T.json ] || nice -n 5 $EV "$@" --seeds 1100 1101 1102 1103 --tag $T --out $D/tune2 >> $D/tune2/run.log 2>&1 || echo "FAIL $T"' < $J
TUNE_DIR=tune2 $PY scripts/CITY_sptsi_tune.py | tee $D/tune2/tune.txt || { echo "TUNE2 FAIL"; exit 1; }
J=$D/conf2_jobs.txt; : > $J
for k in 11 111; do AB=$($PY -c "import json;print(json.load(open('$D/tune2/choice.json'))['$k']['choice'].replace(',',':'))"); TK="n2k:$SP/s3b/prov/fkcl_rlk$k.json:$D/model/n2k_sp$k.pt"
  echo "R_$k --tk none --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J; echo "TSIK2_$k --tk $TK --light RLKQ:$SP/RLK_sp$k.pt:$AB --fleet GLOSAL:0.3" >> $J
  echo "HYBK_$k --tk $TK --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J; echo "ADPK2_$k --tk none --light RLKQ:$SP/RLK_sp$k.pt:$AB --fleet GLOSAL:0.3" >> $J; done
export SS="$(seq -s ' ' 1130 1149)"; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/conf2/$T.json ] || nice -n 5 $EV "$@" --seeds $SS --tag $T --out $D/conf2 >> $D/conf2/run.log 2>&1 || echo "FAIL $T"' < $J
echo "panel done $(date)"; SPTSI_V2=1 $PY scripts/CITY_sptsi_report.py; echo "SPTSI2 done $(date)"
