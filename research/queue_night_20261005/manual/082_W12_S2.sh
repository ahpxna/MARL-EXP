#!/usr/bin/env bash
# W12-3 S2a (PROTOCOL_CITY_WAVE12_20261006, A4): KR-1 -> R, TSIK, TREL on spider 1170-1189 -> matched rate p per signal from TREL -> RREL -> report.
# SMOKE=1: signal 11, seed 1170, into W12_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W12_DIR:-research/city_sim/w12_20261006/s2}; mkdir -p $D/conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd)
SP=research/city_sim/m4_20261004/spider; S4=research/city_sim/w10_20261005/sp4; RL="$PY -u scripts/CITY_w12_release.py scripts/CITY_m4s_tsi_eval.py"
if [ "${SMOKE:-0}" = 1 ]; then LK="11"; CS="1170"; else LK="11 111"; CS="$(seq -s ' ' 1170 1189)"; fi
AB() { [ "$1" = 11 ] && echo "2:0.5" || echo "1:0.5"; }; TK() { echo "n2k:$SP/s3b/prov/fkcl_rlk$1.json:$S4/model/n2k1_sp$1.pt"; }
TSIK() { echo "--tk $(TK $1) --light RLKQ:$SP/RLK_sp$1.pt:$(AB $1) --fleet GLOSAL:0.3"; }
echo "W12-S2 start $(date)"
# KR-1: wrapper with release off == plain evaluator (signal 11, seed 1170)
[ -f $D/conf/KR_tsik_11.json ] || $PY -u scripts/CITY_m4s_tsi_eval.py $(TSIK 11) --seeds 1170 --tag KR_tsik_11 --out $D/conf >> $D/conf/run.log 2>&1 || exit 1
[ -f $D/conf/KR_none_11.json ] || W12_REL=none $RL $(TSIK 11) --seeds 1170 --tag KR_none_11 --out $D/conf >> $D/conf/run.log 2>&1 || exit 1
for k in $LK; do
  [ -f $D/conf/R_$k.json ] || nice -n 5 $PY -u scripts/CITY_m4s_tsi_eval.py --tk none --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3 --seeds $CS --tag R_$k --out $D/conf >> $D/conf/run.log 2>&1 &
  [ -f $D/conf/TSIK_$k.json ] || W12_REL=none nice -n 5 $RL $(TSIK $k) --seeds $CS --tag TSIK_$k --out $D/conf >> $D/conf/run.log 2>&1 &
  [ -f $D/conf/TREL_$k.json ] || W12_REL=targeted nice -n 5 $RL $(TSIK $k) --seeds $CS --tag TREL_$k --out $D/conf >> $D/conf/run.log 2>&1 &
done; wait
for k in $LK; do for a in R TSIK TREL; do [ -f $D/conf/${a}_$k.json ] || { echo "run failed $a $k"; exit 1; }; done; done
for k in $LK; do p=$($PY -c "import json;r=json.load(open('$D/conf/TREL_$k.json'))['rows'];print(sum(x['rel_released'] for x in r)/max(1,sum(x['rel_glide_s'] for x in r)))")
  echo "matched release probability signal $k: $p"; [ -f $D/conf/RREL_$k.json ] || W12_REL=random:$p nice -n 5 $RL $(TSIK $k) --seeds $CS --tag RREL_$k --out $D/conf >> $D/conf/run.log 2>&1 & done; wait
for k in $LK; do [ -f $D/conf/RREL_$k.json ] || { echo "RREL failed $k"; exit 1; }; done; echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W12_SMOKE=$D W12_SEED=1170 $PY scripts/CITY_w12_s2_report.py; else $PY scripts/CITY_w12_s2_report.py; fi || exit 1; echo "W12-S2 done $(date)"
