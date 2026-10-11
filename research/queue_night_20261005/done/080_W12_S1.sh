#!/usr/bin/env bash
# W12-2 S1 (PROTOCOL_CITY_WAVE12_20261006, A2): record R and TSIK (attempt-4) schedules on spider 1170-1189 -> ReplayK replays SIG / FC / ORC on
# each -> KH-1 / KH-1b -> report.  SMOKE=1: signal 11, seed 1170 (full horizon, it is fast), into W12_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W12_DIR:-research/city_sim/w12_20261006/s1}; mkdir -p $D/conf $D/check $D/rec; export XPLAY_TMP=$(cd $D/check && pwd)
SP=research/city_sim/m4_20261004/spider; S4=research/city_sim/w10_20261005/sp4
EV="$PY -u scripts/CITY_m4s_tsi_eval.py"; RK="$PY -u scripts/CITY_w12_replayk.py"
if [ "${SMOKE:-0}" = 1 ]; then LK="11"; CS="1170"; else LK="11 111"; CS="$(seq -s ' ' 1170 1189)"; fi
AB() { [ "$1" = 11 ] && echo "2:0.5" || echo "1:0.5"; }
TK() { echo "n2k:$SP/s3b/prov/fkcl_rlk$1.json:$S4/model/n2k1_sp$1.pt"; }
echo "W12-S1 start $(date)"
for k in $LK; do
  mkdir -p $D/rec/R_$k $D/rec/T_$k
  [ -f $D/conf/REC_R_$k.json ] || nice -n 5 $EV --tk none --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3 --seeds $CS --record $D/rec/R_$k/phases_s{seed}.npz --tag REC_R_$k --out $D/conf >> $D/conf/run.log 2>&1 &
  [ -f $D/conf/REC_T_$k.json ] || nice -n 5 $EV --tk $(TK $k) --light RLKQ:$SP/RLK_sp$k.pt:$(AB $k) --fleet GLOSAL:0.3 --seeds $CS --record $D/rec/T_$k/phases_s{seed}.npz --tag REC_T_$k --out $D/conf >> $D/conf/run.log 2>&1 &
done; wait
for k in $LK; do for a in R T; do [ -f $D/conf/REC_${a}_$k.json ] || { echo "recording failed $a $k"; exit 1; }; done; done; echo "recordings done $(date)"
J=$D/jobs.txt; : > $J
for k in $LK; do for sch in R T; do
  echo "SIG_${sch}_$k scripts/CITY_m4s_tsi_eval.py --tk none --replay-dir $D/rec/${sch}_$k --fleet GLOSAL:0.3" >> $J
  echo "FC_${sch}_$k scripts/CITY_m4s_tsi_eval.py --tk $(TK $k) --replay-dir $D/rec/${sch}_$k --fleet GLOSAL:0.3" >> $J
  echo "ORC_${sch}_$k scripts/CITY_m4s_run.py scripts/CITY_m3_headroom.py --replay-dir $D/rec/${sch}_$k --fleet GLOSAL:0.3" >> $J; done; done
export PY D RK SS="$CS"
xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $RK "$@" --seeds $SS --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "replay failure: stop"; exit 1; }
echo "replays done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W12_SMOKE=$D W12_SEED=1170 $PY scripts/CITY_w12_s1_report.py; else $PY scripts/CITY_w12_s1_report.py; fi || exit 1; echo "W12-S1 done $(date)"
