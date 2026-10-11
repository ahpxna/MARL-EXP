#!/usr/bin/env bash
# W6-5 M2-L (PROTOCOL_CITY_WAVE6_20261005): stage 0 (L1 family on DEV 600-605, SUMO cars) -> L1 tables (8 TRAIN logs per light) -> confirmation
# on 760-779 (L0 = RL-H t4-t8 x F1-B fleets: R0, F0c; L1 lights x F1-B fleets: R1, F0n, F0r) -> report.  SMOKE=1: 300 s, one seed, one light.
set -eo pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W6_DIR:-research/city_sim/w6_20261005/m2l}; mkdir -p $D/check $D/s0 $D/feat $D/tab $D/conf; export XPLAY_TMP=$(cd "$D/check" && pwd)
G=research/city_sim/demand/grid4; TB=research/city_sim/f1b_20261004/prep; FB=research/city_sim/f1b_20261004/train; P=research/city_sim/spat_pilot_20261004/fleets_v11
RUN="$PY -u scripts/CITY_f1a1_run.py"; echo "W6-M2L start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; S0S="600"; TRS="0"; CS="600"; export W6_S0=600; else SM=""; S0S="$(seq -s ' ' 600 605)"; TRS="0 1 2 3 4 5 6 7"; CS="$(seq -s ' ' 760 779)"
  [ -f $G/CONF760_generated ] || { echo "traffic 760-779 not generated (job 051): stop"; exit 1; }; fi
export PY D RUN SM SMOKE
# stage 0
J=$D/s0_jobs.txt; : > $J; for k in 4 5 6 7 8; do echo "S0_RLH_t$k --light RL-H:$k" >> $J; done
$PY -c "
import sys; sys.path.insert(0, '.'); from scripts.CITY_w6_m2l import FAM
for f, sp in FAM.items():
    for i, s in enumerate(sp): print(f'S0_{f}_{i} --light {s}')" >> $J
export SS="$S0S"; xargs -P 8 -L 1 bash -c 'T=$0; [ -f $D/s0/$T.json ] || nice -n 5 $RUN scripts/CITY_eval_f1.py --spat-arm none "$@" --fleet human --seeds $SS $SM --tag $T --out $D/s0 >> $D/s0/run.log 2>&1 || { echo "FAIL $T"; exit 1; }' < $J
$PY scripts/CITY_w6_m2l.py stage0 $D/s0 > $D/s0/stage0.txt || { echo "STAGE0 FAIL"; exit 1; }; cp $D/s0/stage0.json $D/stage0.json; head -8 $D/s0/stage0.txt
# L1 tables
NL=$($PY -c "import json;print(len(json.load(open('$D/stage0.json'))['specs']))"); [ "${SMOKE:-0}" = 1 ] && NL=1
J=$D/feat_jobs.txt; : > $J
for i in $(seq 0 $((NL - 1))); do SPEC=$($PY -c "import json;print(json.load(open('$D/stage0.json'))['specs'][$i])"); for s in $TRS; do echo "j$i $s $SPEC" >> $J; done; done
xargs -P 8 -L 1 bash -c 'j=$0; s=$1; spec=$2; [ -f $D/feat/$j/feat_s$s.npz ] || nice -n 5 $RUN scripts/CITY_n2_collect.py --featlog $D/feat/$j --spat-arm none --light $spec --fleet PL:research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt --seeds $s $SM --tag C_${j}_s$s --out $D/feat/$j >> $D/feat/run.log 2>&1 || { echo "FAIL collect $j $s"; exit 1; }' < $J
for i in $(seq 0 $((NL - 1))); do $PY scripts/CITY_w6_m2l.py fit $D/feat/j$i $D/tab/prov_j$i.json || { echo "FIT FAIL j$i"; exit 1; }; done
# confirmation
J=$D/conf_jobs.txt; : > $J; FP=("213 4" "313 5" "413 6" "513 7"); LTS="4 5 6 7 8"; [ "${SMOKE:-0}" = 1 ] && { FP=("213 4"); LTS="4"; }
for t in $LTS; do for p in "${FP[@]}"; do set -- $p; F=$FB/F1B_s$1_t$2_fleet.pt
  echo "R0_L0t${t}_s$1 scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$t --fleet PL:$F" >> $J
  echo "F0c_L0t${t}_s$1 scripts/CITY_eval_f1b.py --spat-arm fc2:0.1:$TB/prov_rlh${t}_cl.json --light RL-H:$t --fleet PL:$F" >> $J; done; done
for i in $(seq 0 $((NL - 1))); do SPEC=$($PY -c "import json;print(json.load(open('$D/stage0.json'))['specs'][$i])"); for p in "${FP[@]}"; do set -- $p; F=$FB/F1B_s$1_t$2_fleet.pt
  echo "R1_L1j${i}_s$1 scripts/CITY_eval_f1.py --spat-arm none --light $SPEC --fleet PL:$F" >> $J
  echo "F0n_L1j${i}_s$1 scripts/CITY_eval_f1b.py --spat-arm fc2:0.1:$TB/prov_rlh$2_cl.json --light $SPEC --fleet PL:$F" >> $J
  echo "F0r_L1j${i}_s$1 scripts/CITY_eval_f1b.py --spat-arm fc2:0.1:$D/tab/prov_j$i.json --light $SPEC --fleet PL:$F" >> $J; done; done
export SS="$CS"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 1; }' < $J
echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W6_SMOKE=$(dirname $D) W6_SMOKE_SEED=600 $PY scripts/CITY_w6_report_v2.py m2l; else $PY scripts/CITY_w6_report_v2.py m2l; fi; echo "W6-M2L done $(date)"
