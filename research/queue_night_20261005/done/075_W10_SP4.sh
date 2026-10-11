#!/usr/bin/env bash
# W10-5 spider attempt 4 (PROTOCOL_CITY_WAVE10_20261005, A3): N2K logs with TSIK published (TRAIN 0-7) -> refit -> KS-1 -> fresh spider 1170-1189
# -> R / TSIK1 / HYBK1 x lights 11 / 111 x rule fleet -> report (alpha 0.00625); secondary served-answer accounting on TUNE 1100-1101.
# SMOKE=1: 600 s, one light, seed 0 / 1170 into W10_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W10_DIR:-research/city_sim/w10_20261005/sp4}; mkdir -p $D/data $D/model $D/check $D/conf $D/diag/sp; export XPLAY_TMP=$(cd $D/check && pwd)
SP=research/city_sim/m4_20261004/spider; ST=research/city_sim/sptsi_20261005; G=research/city_sim/demand/spider/p2.0; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py
EV="$PY -u scripts/CITY_m4s_tsi_eval.py"; echo "W10-SP4 start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LK="11"; TS="0 1 2 3 4 5 6 7"; CS="1100"; else SM=""; LK="11 111"; TS="0 1 2 3 4 5 6 7"; CS="$(seq -s ' ' 1170 1189)"; fi
AB() { $PY -c "import json;print(json.load(open('$ST/tune/choice.json'))['$1']['choice'].replace(',',':'))"; }
# 1. logs with the attempt-1 TSIK published
J=$D/collect.txt; : > $J; for k in $LK; do for s in $TS; do echo "$k $s $(AB $k)" >> $J; done; done; export PY D SP ST EV SM
xargs -P 6 -L 1 bash -c '[ -f $D/data/k$0/feat_s$1.npz ] || nice -n 5 $EV --tk n2k:$SP/s3b/prov/fkcl_rlk$0.json:$ST/model/n2k_sp$0.pt --light RLKQ:$SP/RLK_sp$0.pt:$2 --fleet GLOSAL:0.3 --featlog $D/data/k$0 --seeds $1 $SM --tag C_k$0_s$1 --out $D/data/k$0 >> $D/data/run.log 2>&1 || { echo "FAIL collect $0 $1"; exit 255; }' < $J || { echo "collection failed: stop"; exit 1; }
# 2. refit, KS-1 parity
for k in $LK; do [ -f $D/model/n2k1_sp$k.pt ] || $PY -u scripts/CITY_n2k.py fit $D/data/k$k $D/model/n2k1_sp$k.pt > $D/model/fit_k$k.log 2>&1 || { echo "refit FAIL $k"; tail -3 $D/model/fit_k$k.log; exit 1; }; done
K1=$(echo $LK | cut -d' ' -f1)
$EV --tk n2k:$SP/s3b/prov/fkcl_rlk$K1.json:$D/model/n2k1_sp$K1.pt --light RLKQ:$SP/RLK_sp$K1.pt:2:0 --fleet GLOSAL:0.3 --featlog $D/check/ks1 --seeds 0 --smoke --tag KS1 --out $D/check > $D/check/ks1.log 2>&1 || { echo "KS1 run FAIL"; exit 1; }
$PY scripts/CITY_n2k.py parity $D/check/ks1 0 $D/model/n2k1_sp$K1.pt | tee $D/check/ks1_parity.txt || { echo "KS-1 FAIL: stop"; exit 1; }
# 3. fresh traffic 1170-1189
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF1170_generated ]; then for s in $(seq 1170 1189); do [ -f $G/rou_s$s.xml ] && { echo "KW10-5 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 1170 1189); do $PY $RT -n research/city_sim/net/spider.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; date > $G/CONF1170_generated; fi
# 4. confirmation
J=$D/conf_jobs.txt; : > $J
for k in $LK; do TK="n2k:$SP/s3b/prov/fkcl_rlk$k.json:$D/model/n2k1_sp$k.pt"; echo "R_$k --tk none --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J
  echo "TSIK1_$k --tk $TK --light RLKQ:$SP/RLK_sp$k.pt:$(AB $k) --fleet GLOSAL:0.3" >> $J; echo "HYBK1_$k --tk $TK --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J; done
export SS="$CS"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $EV "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation failed: stop"; exit 1; }
echo "panel done $(date)"
# 5. secondary: served-answer accounting of the refit forecaster (TUNE 1100-1101)
W="$PY -u scripts/CITY_w10_run.py"; J=$D/diag_jobs.txt; : > $J; DS="1100 1101"; [ "${SMOKE:-0}" = 1 ] && DS="1100"
for k in $LK; do TK="n2k:$SP/s3b/prov/fkcl_rlk$k.json:$D/model/n2k1_sp$k.pt"
  echo "SHADOW1_$k shadow --net spider scripts/CITY_m4s_tsi_eval.py --tk $TK --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J
  echo "HYBK1_$k serve --net spider scripts/CITY_m4s_tsi_eval.py --tk $TK --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J
  echo "TSIK1_$k serve --net spider scripts/CITY_m4s_tsi_eval.py --tk $TK --light RLKQ:$SP/RLK_sp$k.pt:$(AB $k) --fleet GLOSAL:0.3" >> $J; done
echo "FTX plain --net spider scripts/CITY_eval6_lane.py --light FT --fleet GLOSAL:0.3" >> $J; export W DS
xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $D/diag/sp/$T.json ] && exit 0; W10_LOG=$D/diag/sp/served nice -n 5 $W $M "$@" --seeds $DS $SM --record $D/diag/sp/rec/${T}_s{seed}.npz --tag $T --out $D/diag/sp >> $D/diag/sp/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "diag runs failed (secondary): continue"; }
$PY scripts/CITY_w10_diag.py $D/diag > $D/diag/diag.out 2>&1 || echo "secondary diag report failed"
if [ "${SMOKE:-0}" = 1 ]; then W10_SMOKE=$(dirname $D) W10_SEED=1100 $PY scripts/CITY_w10_report2.py sp4; else $PY scripts/CITY_w10_report2.py sp4; fi || exit 1; echo "W10-SP4 done $(date)"
