#!/usr/bin/env bash
# W7-1 FPR (PROTOCOL_CITY_WAVE7_20261005): NEW lights RL-H t9-t13 + NEW fleets R10 s613-s913 (trained in parallel) -> per-light TSI calibration
# from scratch (traces -> open-loop table -> closed-loop c2 prep -> N2 logs -> fit -> KF-2 parity -> adapter tuning) -> fresh traffic 780-799
# -> confirmation (R, TSI, HYB, ADP; 5 x 4 x 20) -> report.  SMOKE=1: one light / fleet, tiny budgets, 600 s, seeds 0-7 / 660.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W7_DIR:-research/city_sim/w7_20261005/fpr}; mkdir -p $D/lights $D/fleets $D/traces/tmp $D/m2b $D/prep $D/cdata $D/cmodel $D/check $D/tune $D/conf; export XPLAY_TMP=$PWD/$D/check
export W7_LIGHTS=$PWD/$D/lights W7_FPR_DIR=$PWD/$D; G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py
DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt; RUN="$PY -u scripts/CITY_w7_run.py"; echo "W7-FPR start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="9"; FS="613"; LEP=1; FEP=1; TS="0 1 2 3 4 5 6 7"; TUNES="660"; CS="660"; export W7_TUNE_SEEDS=660 W7_PREP_N=1 W7_PREP_END=300
else SM=""; LT="9 10 11 12 13"; FS="613 713 813 913"; LEP=120; FEP=400; TS="0 1 2 3 4 5 6 7"; TUNES="660 661 662 663"; CS="$(seq -s ' ' 780 799)"; fi
# 1. training (lights and fleets in parallel)
for k in $LT; do [ -f $D/lights/RL-H_t$k.pt ] || nice -n 5 $PY -u scripts/CITY_q7b_contract.py --out $D/lights --train-light RL-H_t$k --t $k --episodes $LEP $SM > $D/lights/train_t$k.out 2>&1 & done
for s in $FS; do [ -f $D/fleets/L11_s${s}_fleet.pt ] || nice -n 5 $PY -u scripts/CITY_fleet_train_v11_ppo.py --spat on --seed $s --episodes $FEP --name L11_s$s --out $D/fleets --resume $SM > $D/fleets/L11_s$s.out 2>&1 & done
wait; echo "training done $(date)"
$PY - <<PYC || { echo "KF-1 FAIL: stop"; exit 1; }
import json, hashlib, sys
ok = True; out = []
for k in "$LT".split():
    f = '$D/lights/RL-H_t%s.pt' % k; n = len(json.load(open('$D/lights/RL-H_t%s.log.json' % k))); ok &= n == $LEP; out.append(f'light t{k}: episodes {n} sha {hashlib.sha256(open(f, "rb").read()).hexdigest()[:16]}')
for s in "$FS".split():
    f = '$D/fleets/L11_s%s_fleet.pt' % s; n = len(json.load(open('$D/fleets/L11_s%s.log.json' % s))); ok &= n == $FEP; out.append(f'fleet s{s}: episodes {n} sha {hashlib.sha256(open(f, "rb").read()).hexdigest()[:16]}')
t = '\n'.join(out) + f'\nKF-1: {"PASS" if ok else "FAIL"}\n'; open('$D/check/kf1.txt', 'w').write(t); print(t); sys.exit(0 if ok else 1)
PYC
# 2-3. traces and open-loop tables
for k in $LT; do [ -f $D/traces/fit_RLH$k.json ] || nice -n 5 $RUN scripts/CITY_eval4_sigma.py --sigma 0.3 --light RL-H:$k --fleet L-ACT:0 --guard always --seeds $TS $SM --record $D/traces/rlh${k}_s{seed}.npz --tag fit_RLH$k --out $D/traces >> $D/traces/run.log 2>&1 & done; wait
for k in $LT; do F=""; for s in $TS; do F="$F $D/traces/rlh${k}_s$s.npz"; done; $RUN scripts/CITY_spat_forecast.py fit $k $D/m2b/forecast_rlh$k.json $F || { echo "open-loop fit FAIL t$k"; exit 1; }; done
# 4. closed-loop c2 prep
for k in $LT; do [ -f $D/prep/prov_rlh${k}_cl.json ] || nice -n 5 $PY -u scripts/CITY_w7_prep.py $k $D/prep > $D/prep/prep_k$k.out 2>&1 & done; wait
NF=8; [ "${SMOKE:-0}" = 1 ] && NF=1
for k in $LT; do $PY -c "
import json; T = json.load(open('$D/prep/prov_rlh${k}_cl.json')); assert len(T['per']) == 16 and T['n_files'] == $NF, (len(T['per']), T['n_files']); print('KF-3 t$k: 16 lights x', T['n_files'], 'files')" || { echo "KF-3 FAIL t$k"; exit 1; }; done
# 5. fresh confirmation traffic 780-799 (not in smoke)
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF780_generated ]; then for s in $(seq 780 799); do [ -f $G/rou_s$s.xml ] && { echo "KW-0 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 780 799); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; date > $G/CONF780_generated; fi
# 6-7. N2 feature logs and fits
J=$D/collect_jobs.txt; : > $J; for k in $LT; do for s in $TS; do echo "$k $s" >> $J; done; done
export PY D RUN SM DEV; xargs -P 8 -L 1 bash -c '[ -f $D/cdata/c2_t$0/feat_s$1.npz ] || nice -n 5 $RUN scripts/CITY_n2_collect.py --featlog $D/cdata/c2_t$0 --spat-arm fc2:0.1:$D/prep/prov_rlh$0_cl.json --light RL-H:$0 --fleet PL:$DEV --seeds $1 $SM --tag C_t$0_s$1 --out $D/cdata/c2_t$0 >> $D/cdata/run.log 2>&1 || { echo "FAIL collect $0 $1"; exit 255; }' < $J || { echo "collection failure: stop"; exit 1; }
for k in $LT; do [ -f $D/cmodel/n2_k$k.pt ] || $PY -u scripts/CITY_n2_fit.py $k $D/cdata/c2_t$k $D/cmodel > $D/cmodel/fit_t$k.log 2>&1 || { echo "FIT FAIL t$k"; exit 1; }; done
# KF-2 parity on the first new light
K1=$(echo $LT | cut -d' ' -f1); F1=$(echo $FS | cut -d' ' -f1); K=$D/check/kf2_t$K1; mkdir -p $K
$RUN scripts/CITY_eval_n2.py --n2 0.5:$D/cmodel/n2_k$K1.pt --featlog $K --light RL-H:$K1 --fleet PL:$D/fleets/L11_s${F1}_fleet.pt --seeds 0 --smoke --tag KF2_n2 --out $K > $K/run.log 2>&1 || { echo "KF-2 run FAIL"; exit 1; }
$PY scripts/CITY_n2_parity.py $K 0 $D/cmodel/n2_k$K1.pt | tee $D/check/kf2.txt || { echo "KF-2 FAIL: stop"; exit 1; }
# 8. per-light adapter tuning (TSI-2 grid and rule)
J=$D/tune_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$DEV"; echo "R_t$k scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  for ab in "1 0" "1.5 0" "2 0" "1 0.25" "1.5 0.25" "2 0.25" "1 0.5" "1.5 0.5" "2 0.5" "3 0.5"; do set -- $ab; T=$(echo "T_t${k}_a$1_b$2" | tr '.' 'p')
    echo "$T scripts/CITY_eval_n4.py --n4 0.5:hyb:$D/prep/prov_rlh${k}_cl.json:$D/cmodel/n2_k$k.pt $F --light-obs q:$1:$2" >> $J; done; done
export SS="$TUNES"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/tune/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/tune >> $D/tune/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "tuning failure: stop"; exit 1; }
$PY scripts/CITY_w7_tune.py $D $LT | tee $D/tune/tune.txt || { echo "TUNE FAIL"; exit 1; }
# 9. confirmation
J=$D/conf_jobs.txt; : > $J
for k in $LT; do AB=$($PY -c "import json;print(json.load(open('$D/tune/choice.json'))['$k']['choice'].replace(',',':'))"); N4="--n4 0.5:hyb:$D/prep/prov_rlh${k}_cl.json:$D/cmodel/n2_k$k.pt"
  for s in $FS; do F="--light RL-H:$k --fleet PL:$D/fleets/L11_s${s}_fleet.pt"
    echo "R_t${k}_s$s scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "TSI_t${k}_s$s scripts/CITY_eval_n4.py $N4 $F --light-obs q:$AB" >> $J
    echo "HYB_t${k}_s$s scripts/CITY_eval_n4.py $N4 $F" >> $J; echo "ADP_t${k}_s$s scripts/CITY_eval_f1.py --spat-arm none $F --light-obs q:$AB" >> $J; done; done
export SS="$CS"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation failure: stop"; exit 1; }
echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W7_SMOKE=$(dirname $D) W7_SEED=660 $PY scripts/CITY_w7_report.py fpr; else $PY scripts/CITY_w7_report.py fpr; fi || exit 1; echo "W7-FPR done $(date)"
