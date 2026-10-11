#!/usr/bin/env bash
# F1-B chain (PROTOCOL_CITY_F1B_20261004): KB0-5 -> DEV traffic 550-564 -> B1 (55 jobs) -> B1 report -> B2 prep (c2) -> 4 x 200-episode scratch -> B2 DEV (25 jobs)
# -> B2 report = ONE decision.  Stops at the first failed check.  B0 offline (KB0-1/2/4) and online (KB0-3) checks were run before this chain.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/f1b_20261004; R=scripts/CITY_f1a1_run.py
A=research/city_sim/f1a1_20261004; RULE=research/city_sim/f1_20261004/train/RULE0_fleet.pt; P=research/city_sim/spat_pilot_20261004/fleets_v11; G=research/city_sim/demand/grid4
RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; mkdir -p $D/check/tmp $D/b1/tmp $D/b2/tmp $D/prep $D/train; echo "start $(date)"
grep -q "B0 OFFLINE: PASS" $D/check/b0_offline.txt && grep -q "KB0-3: PASS" $D/check/b0_probe_t4.txt || { echo "B0 not passed: stop"; exit 1; }
# KB0-5: none arm == the frozen evaluator's none arm; zero-residual trainer under c2 (0 episodes) == RULE0 under c2 (TRAIN seed 0)
ck() { XPLAY_TMP=$PWD/$D/check/tmp nice -n 5 $PY -u $R "$@" --seeds 0 --out $D/check >> $D/check/run.log 2>&1; }
[ -f $D/train/Z0_fleet.pt ] || $PY -u $R scripts/CITY_fleet_train_f1b.py --seed 213 --light-k 4 --init scratch --table $A/prep/prov_rlh4_cl.json --q 0.1 --episodes 0 --name Z0 --out $D/train > $D/train/Z0.out 2>&1
ck scripts/CITY_eval_f1b.py --spat-arm none --light RL-H:4 --fleet PL:$P/L11_s13_fleet.pt --tag K_none_new & ck scripts/CITY_eval_f1.py --spat-arm none --light RL-H:4 --fleet PL:$P/L11_s13_fleet.pt --tag K_none_old &
ck scripts/CITY_eval_f1b.py --spat-arm fc2:0.1:$A/prep/prov_rlh4_cl.json --light RL-H:4 --fleet PL:$RULE --tag K_rule0_c2 & ck scripts/CITY_eval_f1b.py --spat-arm fc2:0.1:$A/prep/prov_rlh4_cl.json --light RL-H:4 --fleet PL:$D/train/Z0_fleet.pt --tag K_zero_c2 & wait
$PY - <<PYC || { echo "KB0-5 FAIL: stop"; exit 1; }
import sys; sys.path.insert(0, '.')
from scripts.CITY_spatp_report import rows
C = rows('$D/check'); Q = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'fuel', 'teleports')
a = all(C['K_none_new'][0][q] == C['K_none_old'][0][q] for q in Q); b = all(C['K_rule0_c2'][0][q] == C['K_zero_c2'][0][q] for q in Q)
t = f'KB0-5 none arm new == frozen evaluator: {a}; zero-residual trainer (0 episodes) under c2 == RULE0 under c2: {b}\nKB0-5: {"PASS" if a and b else "FAIL"}\n'
open('$D/check/kb0_5.txt', 'w').write(t); print(t); sys.exit(0 if a and b else 1)
PYC
if [ ! -f $D/check/traffic_generated ]; then
  for s in $(seq 550 564); do [ -f $G/rou_s$s.xml ] && { echo "DEV traffic $s existed before generation: stop"; exit 1; }; done
  for s in $(seq 550 564); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger \
    --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; echo "550-564 generated $(date)" | tee $D/check/traffic_generated; fi
S="$(seq -s ' ' 550 564)"; export PY R S D
run_jobs() { xargs -P 8 -L 1 bash -c 'O=$0; T=$1; shift 1; [ -f $D/$O/$T.json ] || XPLAY_TMP=$PWD/$D/$O/tmp nice -n 5 $PY -u $R scripts/CITY_eval_f1b.py "$@" --seeds $S --tag $T --out $D/$O >> $D/$O/run.log 2>&1 || echo "FAIL $T"'; }
J=$D/b1/jobs.txt; : > $J
for l in 4 5 6 7 8; do TB=$A/prep/prov_rlh${l}_cl.json; echo "b1 R_t$l --spat-arm none --light RL-H:$l --fleet PL:$P/L11_s13_fleet.pt" >> $J
  echo "b1 RULEo_t$l --spat-arm fcc:0.1:$TB --light RL-H:$l --fleet PL:$RULE" >> $J; echo "b1 RULEn_t$l --spat-arm fc2:0.1:$TB --light RL-H:$l --fleet PL:$RULE" >> $J
  for p in "213 4" "313 5" "413 6" "513 7"; do set -- $p; F=$A/train/F1s_s$1_t$2_fleet.pt
    echo "b1 Ao_s$1_on_t$l --spat-arm fcc:0.1:$TB --light RL-H:$l --fleet PL:$F" >> $J; echo "b1 An_s$1_on_t$l --spat-arm fc2:0.1:$TB --light RL-H:$l --fleet PL:$F" >> $J; done; done
run_jobs < $J; echo "B1 done $(date)"; $PY scripts/CITY_f1b_report.py b1 || exit 1
# ---- B2: prep with c2, check the tables, train, DEV evaluation, ONE decision
for l in 4 5 6 7 8; do [ -f $D/prep/prov_rlh${l}_cl.json ] || nice -n 5 $PY -u scripts/CITY_f1b_prep.py $l $D/prep > $D/prep/prep_k$l.out 2>&1 & done; wait
$PY -c "
import json, sys
for l in (4, 5, 6, 7, 8):
    T = json.load(open('$D/prep/prov_rlh%d_cl.json' % l)); assert len(T['per']) == 16 and T['n_files'] == 8, l
print('KB2-0 F1-B prep tables: 16 lights x 8 files each')" || { echo "KB2-0 FAIL"; exit 1; }
for p in "213 4" "313 5" "413 6" "513 7"; do set -- $p; [ -f $D/train/F1B_s$1_t$2_fleet.pt ] || nice -n 5 $PY -u $R scripts/CITY_fleet_train_f1b.py --seed $1 --light-k $2 --init scratch \
  --table $D/prep/prov_rlh$2_cl.json --q 0.1 --episodes 200 --name F1B_s$1_t$2 --out $D/train > $D/train/F1B_s$1_t$2.out 2>&1 & done; wait; echo "B2 training done $(date)"
for p in "213 4" "313 5" "413 6" "513 7"; do set -- $p; [ -f $D/train/F1B_s$1_t$2_fleet.pt ] || { echo "missing F1B_s$1_t$2"; exit 1; }; done
J=$D/b2/jobs.txt; : > $J
for l in 4 5 6 7 8; do TB=$D/prep/prov_rlh${l}_cl.json; echo "b2 RULEb_t$l --spat-arm fc2:0.1:$TB --light RL-H:$l --fleet PL:$RULE" >> $J
  for p in "213 4" "313 5" "413 6" "513 7"; do set -- $p; echo "b2 Bn_s$1_on_t$l --spat-arm fc2:0.1:$TB --light RL-H:$l --fleet PL:$D/train/F1B_s$1_t$2_fleet.pt" >> $J; done; done
run_jobs < $J; echo "B2 eval done $(date)"; $PY scripts/CITY_f1b_report.py b2; echo "F1-B chain done $(date)"
