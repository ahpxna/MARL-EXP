#!/usr/bin/env bash
# W6-2 / W6-3 H4 + H5 (PROTOCOL_CITY_WAVE6_20261005): R reference rows (TRAIN 0-7 under RL-H t4-t7, for H5) -> 8 trainings in parallel
# (H4: R10 init + std / value reset; H5: scratch + Lagrangian; 200 episodes each) -> confirmation on 760-779 (R, F1B, H4, H5) -> report.
# SMOKE=1: 1 episode of 300 s, one light / fleet / seed.
set -eo pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W6_DIR:-research/city_sim/w6_20261005/h45}; mkdir -p $D/check $D/rref $D/train $D/conf; export XPLAY_TMP=$(cd "$D/check" && pwd)
G=research/city_sim/demand/grid4; TB=research/city_sim/f1b_20261004/prep; FB=research/city_sim/f1b_20261004/train; P=research/city_sim/spat_pilot_20261004/fleets_v11
RUN="$PY -u scripts/CITY_f1a1_run.py"; echo "W6-H45 start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; EP=1; PAIRS=("213 4"); CS="600"; else SM=""; EP=200; PAIRS=("213 4" "313 5" "413 6" "513 7"); CS="$(seq -s ' ' 760 779)"
  [ -f $G/CONF760_generated ] || { echo "traffic 760-779 not generated (job 051): stop"; exit 1; }; fi
export PY D RUN SM
# R reference for H5: TRAIN seeds 0-7 under RL-H:k, fleet sigma* (no SPaT)
for p in "${PAIRS[@]}"; do set -- $p; [ -f $D/rref/R_t$2.json ] || nice -n 5 $RUN scripts/CITY_eval_h5_reference.py --spat-arm none --light RL-H:$2 --fleet PL:$P/L11_s13_fleet.pt --seeds 0 1 2 3 4 5 6 7 $SM --tag R_t$2 --out $D/rref >> $D/rref/run.log 2>&1 & done; wait
for p in "${PAIRS[@]}"; do set -- $p; $PY -c "
import json; r = json.load(open('$D/rref/R_t$2.json'))['rows']; assert len(r) == 8 and {x['seed'] for x in r} == set(range(8)); h={x['h5_reference_horizon'] for x in r}; assert len(h)==1; json.dump(dict(horizon=h.pop(),light_k=$2,timeloss_agent={str(x['seed']):x['timeloss_agent'] for x in r}), open('$D/rref/rref_t$2.json', 'w'))" || { echo "RREF FAIL t$2"; exit 1; }; done
# trainings (8 in parallel)
for p in "${PAIRS[@]}"; do set -- $p
  [ -f $D/train/H4_s$1_t$2_fleet.pt ] || nice -n 5 $RUN scripts/CITY_fleet_train_h45.py --mode h4 --seed $1 --light-k $2 --init $P/L11_s$1_fleet.pt --table $TB/prov_rlh$2_cl.json --q 0.1 --episodes $EP $SM --name H4_s$1_t$2 --out $D/train > $D/train/H4_s$1_t$2.out 2>&1 &
  [ -f $D/train/H5_s$1_t$2_fleet.pt ] || nice -n 5 $RUN scripts/CITY_fleet_train_h45.py --mode h5 --seed $1 --light-k $2 --init scratch --rref $D/rref/rref_t$2.json --table $TB/prov_rlh$2_cl.json --q 0.1 --episodes $EP $SM --name H5_s$1_t$2 --out $D/train > $D/train/H5_s$1_t$2.out 2>&1 &
done; wait; echo "trainings done $(date)"
for p in "${PAIRS[@]}"; do set -- $p; for h in H4 H5; do [ -f $D/train/${h}_s$1_t$2_fleet.pt ] || { echo "missing ${h}_s$1_t$2: stop"; exit 1; }; done; done
# confirmation
J=$D/conf_jobs.txt; : > $J; LTS="4 5 6 7 8"; [ "${SMOKE:-0}" = 1 ] && LTS="4"
for t in $LTS; do for p in "${PAIRS[@]}"; do set -- $p; TBL=$TB/prov_rlh${t}_cl.json
  echo "R_t${t}_s$1 scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$t --fleet PL:$P/L11_s$1_fleet.pt" >> $J
  echo "F1B_t${t}_s$1_t$2 scripts/CITY_eval_f1b.py --spat-arm fc2:0.1:$TBL --light RL-H:$t --fleet PL:$FB/F1B_s$1_t$2_fleet.pt" >> $J
  for h in H4 H5; do echo "${h}_t${t}_s$1_t$2 scripts/CITY_eval_f1b.py --spat-arm fc2:0.1:$TBL --light RL-H:$t --fleet PL:$D/train/${h}_s$1_t$2_fleet.pt" >> $J; done; done; done
export SS="$CS"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 1; }' < $J
echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W6_SMOKE=$(dirname $D) W6_SMOKE_SEED=600 $PY scripts/CITY_w6_report_v2.py h45; else $PY scripts/CITY_w6_report_v2.py h45; fi; echo "W6-H45 done $(date)"
