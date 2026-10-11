#!/usr/bin/env bash
# F1-A1 chain (Amendment F1-A1): traces -> open-loop fit -> KA-2 -> closed-loop prep -> KA-1/KA-3 -> traffic 530-549 (KA-4) -> 4 scratch runs
# -> crossed evaluation (30 jobs x 20 traffic, 10 at a time) -> report.  Stops at the first failed check.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/f1a1_20261004; R=scripts/CITY_f1a1_run.py
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py
Q=$($PY -c "import json;print(json.load(open('research/city_sim/f1_20261004/prov/locked.json'))['q'])"); RULE=research/city_sim/f1_20261004/train/RULE0_fleet.pt
P=research/city_sim/spat_pilot_20261004; mkdir -p $D/traces/tmp $D/eval/tmp; echo "start $(date) q $Q"
for t in 4 5 6 7 8; do [ -f $D/traces/fit_RLH$t.json ] || XPLAY_TMP=$PWD/$D/traces/tmp nice -n 5 $PY -u $R scripts/CITY_eval4_sigma.py --sigma 0.3 --light RL-H:$t --fleet L-ACT:0 --guard always \
  --seeds 0 1 2 3 4 5 6 7 --record $D/traces/rlh${t}_s{seed}.npz --tag fit_RLH$t --out $D/traces >> $D/traces/run.log 2>&1 & done; wait; echo "traces done $(date)"
for t in 4 5 6 7 8; do $PY $R scripts/CITY_spat_forecast.py fit $t $D/m2b/forecast_rlh$t.json $D/traces/rlh${t}_s{0,1,2,3,4,5,6,7}.npz || exit 1; done
$PY scripts/CITY_f1a1_checks.py conv || { echo "KA-2 FAIL: stop"; exit 1; }
for t in 4 5 6 7 8; do [ -f $D/prep/prov_rlh${t}_cl.json ] || nice -n 5 $PY -u scripts/CITY_f1a1_prep.py $t $D/prep > $D/prep/prep_k$t.out 2>&1 & done; wait; echo "prep done $(date)"
$PY scripts/CITY_f1a1_checks.py tables || { echo "KA-1/KA-3 FAIL: stop"; exit 1; }
if [ ! -f $D/check/traffic_generated ]; then
  for s in $(seq 530 549); do [ -f $G/rou_s$s.xml ] && { echo "KA-4 FAIL: $G/rou_s$s.xml existed before generation"; exit 1; }; done
  for s in $(seq 530 549); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger \
    --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  echo "KA-4 PASS: 530-549 generated $(date)" | tee $D/check/traffic_generated; fi
for p in "213 4" "313 5" "413 6" "513 7"; do set -- $p; nice -n 5 $PY -u $R scripts/CITY_fleet_train_f1.py --seed $1 --light-k $2 --init scratch --table $D/prep/prov_rlh$2_cl.json \
  --q $Q --episodes 200 --name F1s_s$1_t$2 --out $D/train > $D/train/F1s_s$1_t$2.out 2>&1 & done; wait; echo "training done $(date)"
for p in "213 4" "313 5" "413 6" "513 7"; do set -- $p; [ -f $D/train/F1s_s$1_t$2_fleet.pt ] || { echo "missing fleet F1s_s$1_t$2"; exit 1; }; done
S="$(seq -s ' ' 530 549)"; J=$D/eval/jobs.txt; mkdir -p $D/eval/tmp; : > $J
for t in 4 5 6 7 8; do echo "none RL-H:$t PL:$P/fleets_v11/L11_s13_fleet.pt R_t$t" >> $J; echo "fcc:$Q:$D/prep/prov_rlh${t}_cl.json RL-H:$t PL:$RULE RULE_t$t" >> $J
  for p in "213 4" "313 5" "413 6" "513 7"; do set -- $p; echo "fcc:$Q:$D/prep/prov_rlh${t}_cl.json RL-H:$t PL:$D/train/F1s_s$1_t$2_fleet.pt F1s_s$1_on_t$t" >> $J; done; done
export PY R D S; xargs -P 10 -L 1 sh -c '[ -f $D/eval/$3.json ] || XPLAY_TMP=$PWD/$D/eval/tmp nice -n 5 $PY -u $R scripts/CITY_eval_f1.py --spat-arm $0 --light $1 --fleet $2 --seeds $S --tag $3 --out $D/eval >> $D/eval/run.log 2>&1 || echo "FAIL $3"' < $J
echo "eval done $(date)"; $PY scripts/CITY_f1a1_report.py; echo "F1-A1 chain done $(date)"
