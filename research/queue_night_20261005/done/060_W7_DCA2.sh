#!/usr/bin/env bash
# W7-2 DCA2 (PROTOCOL_CITY_WAVE7_20261005): KW7-1 (zero transform == HYB) -> faithful DC-Ada tuning per light t4-t8 (176 truncated rollouts each,
# 5 in parallel) -> confirmation on 760-779 (R, TSI2, DCA2 x 5 lights x 4 fleets) -> report (+ KW7-2).  SMOKE=1: tiny budget, 600 s, one cell.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W7_DIR:-research/city_sim/w7_20261005/dca2}; mkdir -p $D/check $D/tune $D/conf; export XPLAY_TMP=$PWD/$D/check
G=research/city_sim/demand/grid4; P=research/city_sim/spat_pilot_20261004/fleets_v11; TB=research/city_sim/f1b_20261004/prep
MOD=research/city_sim/tsi_20261005/cmodel/c2; CH=research/city_sim/tsi2_20261005/tune/choice.json; RUN="$PY -u scripts/CITY_f1a1_run.py"; echo "W7-DCA2 start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; export DCA2_SMOKE=1; LTS="4"; FLS="s213"; CS="660"; else SM=""; LTS="4 5 6 7 8"; FLS="s213 s313 s413 s513"; CS="$(seq -s ' ' 760 779)"
  [ -f $G/CONF760_generated ] || { echo "traffic 760-779 missing: stop"; exit 1; }; fi
$PY -c "
import sys, torch; sys.path.insert(0, '.')
import scripts.CITY_dcada_layer as L, scripts.CITY_q7_cross_version as Q7
torch.save({i: torch.zeros(L.NPARAM) for i in Q7.NetInfo(Q7.NET_S).tls}, '$D/check/zero.pt')" || exit 1
F="--light RL-H:4 --fleet PL:$P/L11_s13_fleet.pt"; N4="--n4 0.5:hyb:$TB/prov_rlh4_cl.json:$MOD/n2_k4.pt"
[ -f $D/check/K_HYB.json ] || $RUN scripts/CITY_eval_n4.py $N4 $F --seeds 660 --smoke --tag K_HYB --out $D/check >> $D/check/run.log 2>&1 || exit 1
[ -f $D/check/K_Z.json ] || DCA2_PARAMS=$D/check/zero.pt $RUN scripts/CITY_eval_dca2.py $N4 $F --seeds 660 --smoke --tag K_Z --out $D/check >> $D/check/run.log 2>&1 || exit 1
$PY - <<PYC || { echo "KW7-1 FAIL: stop"; exit 1; }
import json, sys
a = json.load(open('$D/check/K_HYB.json'))['rows'][0]; b = json.load(open('$D/check/K_Z.json'))['rows'][0]; Q = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'fuel', 'teleports', 'unfinished')
ok = all(a[q] == b[q] for q in Q); t = f'KW7-1 zero DC-Ada transform == HYB (smoke seed 660, t4): {ok}\nKW7-1: {"PASS" if ok else "FAIL"}\n'; open('$D/check/kw7_1.txt', 'w').write(t); print(t); sys.exit(0 if ok else 1)
PYC
for t in $LTS; do [ -f $D/tune/dca2_t$t.json ] || nice -n 5 $PY -u scripts/CITY_w7_dca2_tune.py $t $D/tune > $D/tune/tune_t$t.log 2>&1 & done; wait
for t in $LTS; do [ -f $D/tune/dca2_params_t$t.pt ] || { echo "tuning failed t$t: stop"; exit 1; }; done; echo "DCA2 tuning done $(date)"
J=$D/conf_jobs.txt; : > $J
for t in $LTS; do AB=$($PY -c "import json;print(json.load(open('$CH'))['$t']['choice'].replace(',',':'))"); N4="--n4 0.5:hyb:$TB/prov_rlh${t}_cl.json:$MOD/n2_k$t.pt"
  for fl in $FLS; do F="--light RL-H:$t --fleet PL:$P/L11_${fl}_fleet.pt"
    echo "R_t${t}_${fl} none scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "TSI2_t${t}_${fl} none scripts/CITY_eval_n4.py $N4 $F --light-obs q:$AB" >> $J
    echo "DCA2_t${t}_${fl} $D/tune/dca2_params_t$t.pt scripts/CITY_eval_dca2.py $N4 $F" >> $J; done; done
export PY D RUN SM SS="$CS"; unset DCA2_SMOKE
xargs -P 6 -L 1 bash -c 'T=$0; PP=$1; shift; [ -f $D/conf/$T.json ] && exit 0; if [ "$PP" = none ]; then nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1; else DCA2_PARAMS=$PP nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1; fi || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation job failure: stop"; exit 1; }
echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W7_SMOKE=$(dirname $D) W7_SEED=660 $PY scripts/CITY_w7_report.py dca2; else $PY scripts/CITY_w7_report.py dca2; fi || exit 1; echo "W7-DCA2 done $(date)"
