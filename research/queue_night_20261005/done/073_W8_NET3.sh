#!/usr/bin/env bash
# W8-4 NET3 (PROTOCOL_CITY_WAVE8_20261005): third network rand3, the whole pipeline with NEW policies.
# demand period (FT city TL near grid4's) -> traffic panels -> train 5 fleets (N3_s13 dev + s213..s513) and 5 lights (RL-H t21..t25) in parallel
# -> M1 (DEV) / M2 (DEV) descriptive -> TSI calibration per light -> confirmation on fresh rand3 700-719 (R, TSI, HYB, ADP) -> report.
# SMOKE=1: tiny budgets, one light / fleet, 300-600 s, seeds 0-7 / 660.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
N=${W8_DIR:-research/city_sim/w8_20261005/net3}; mkdir -p $N/lights $N/fleets $N/traces $N/m2b $N/prep $N/cdata $N/cmodel $N/check $N/tune $N/conf $N/dev $N/period
export XPLAY_TMP=$PWD/$N/check N3_DIR=$PWD/$N N3_LIGHTS=$PWD/$N/lights; G=${N3_DEMAND:-research/city_sim/demand/rand3}; mkdir -p $G
RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; NET=research/city_sim/net/rand3.net.xml; RUN="$PY -u scripts/CITY_n3_run.py"
export N3_ROU=$PWD/$G/rou_s{}.xml; echo "W8-NET3 start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="21"; FS="213"; LEP=1; FEP=1; TS="0 1 2 3 4 5 6 7"; DEVS="600"; TUNES="660"; CS="660"; export W7_TUNE_SEEDS=660 N3_PREP_N=1 N3_PREP_END=300
else SM=""; LT="21 22 23 24 25"; FS="213 313 413 513"; LEP=120; FEP=400; TS="0 1 2 3 4 5 6 7"; DEVS="600 601 602 603 604 605"; TUNES="660 661 662 663"; CS="$(seq -s ' ' 700 719)"; fi
gen() { per=$1; shift; for s in "$@"; do [ -f $G/rou_s$s.xml ] && continue; $PY $RT -n $NET -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period $per > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; }
# 0. demand period: FT city TL on TRAIN seed 0 closest to grid4's (registered rule)
if [ ! -f $N/period/choice.txt ]; then
  [ -n "$(ls $G/rou_s*.xml 2>/dev/null)" ] && [ "${SMOKE:-0}" != 1 ] && { echo "KW-0 FAIL: rand3 demand existed before the period choice"; exit 1; }
  $PY -u scripts/CITY_eval_f1.py --spat-arm none --light FT --fleet human --seeds 0 $SM --tag G4FT --out $N/period > $N/period/run.log 2>&1 || { echo "grid4 FT ref FAIL"; exit 1; }
  for per in 1.6 2.0 2.5 3.0 4.0 5.0; do d=$N/period/p$per; mkdir -p $d; [ -f $d/rou_s0.xml ] || $PY $RT -n $NET -o $d/trips_s0.xml -r $d/rou_s0.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed 0 --min-distance 300 --period $per > /dev/null 2>&1
    N3_ROU=$PWD/$d/rou_s{}.xml $RUN scripts/CITY_eval_f1.py --spat-arm none --light FT --fleet human --seeds 0 $SM --tag FT_p$per --out $N/period >> $N/period/run.log 2>&1 || { echo "period run FAIL $per"; exit 1; }; done
  $PY - <<PYC || { echo "period choice FAIL"; exit 1; }
import json
g = json.load(open('$N/period/G4FT.json'))['rows'][0]['timeloss']; c = {p: json.load(open(f'$N/period/FT_p{p}.json'))['rows'][0]['timeloss'] for p in ('1.6', '2.0', '2.5', '3.0', '4.0', '5.0')}
best = min(c, key=lambda p: abs(c[p] - g)); ok = abs(c[best] - g) <= 0.3 * g
t = f'grid4 FT city TL (seed 0, smoke horizon) {g:.2f}; rand3 by period {json.dumps({k: round(v, 2) for k, v in c.items()})}; chosen period {best}; within +-30 %: {ok}\n'
open('$N/period/choice.txt', 'w').write(best + '\n'); open('$N/period/report.txt', 'w').write(t); print(t)
PYC
fi
PER=$(cat $N/period/choice.txt); echo "period $PER"
gen $PER $TS; gen $PER $DEVS; gen $PER $TUNES; gen $PER $CS; echo "rand3 panels ready $(date)"
# 1. training: 5 fleets (dev N3_s13 + confirmation) and 5 lights, in parallel
for s in 13 $FS; do [ -f $N/fleets/N3_s${s}_fleet.pt ] || nice -n 5 $RUN scripts/CITY_fleet_train_v11_ppo.py --spat on --seed $s --episodes $FEP --name N3_s$s --out $N/fleets --resume $SM > $N/fleets/N3_s$s.out 2>&1 & done
for k in $LT; do [ -f $N/lights/RL-H_t$k.pt ] || nice -n 5 $RUN scripts/CITY_q7b_contract.py --out $N/lights --train-light RL-H_t$k --t $k --episodes $LEP $SM > $N/lights/train_t$k.out 2>&1 & done
wait; for s in 13 $FS; do [ -f $N/fleets/N3_s${s}_fleet.pt ] || { echo "missing fleet N3_s$s: stop"; exit 1; }; done; for k in $LT; do [ -f $N/lights/RL-H_t$k.pt ] || { echo "missing light t$k: stop"; exit 1; }; done; echo "training done $(date)"
export PY N RUN SM
# 2. M1 / M2 on DEV (descriptive): FT sigma* vs FT + program SPaT; learned light R vs naive program SPaT
J=$N/dev_jobs.txt; : > $J
for s in $FS; do F=$N/fleets/N3_s${s}_fleet.pt; echo "SIGFT_s$s scripts/CITY_eval_f1.py --spat-arm none --light FT --fleet PL:$F" >> $J; echo "FLTFT_s$s scripts/CITY_eval6_v11.py --light FT --fleet PL:$F" >> $J
  for k in $LT; do echo "R_t${k}_s$s scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$k --fleet PL:$F" >> $J; echo "NAIVE_t${k}_s$s scripts/CITY_eval6_v11.py --light RL-H:$k --fleet PL:$F" >> $J; done; done
for k in $LT; do echo "LA_t$k scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$k --fleet human" >> $J; done; echo "FTA scripts/CITY_eval_f1.py --spat-arm none --light FT --fleet human" >> $J
export SS="$DEVS"; xargs -P 8 -L 1 bash -c 'T=$0; [ -f $N/dev/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $N/dev >> $N/dev/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "DEV runs failed: stop"; exit 1; }
# 3. TSI calibration per light (as W7-1, on rand3, dev fleet N3_s13)
DEV=$N/fleets/N3_s13_fleet.pt
for k in $LT; do [ -f $N/traces/fit_RLH$k.json ] || nice -n 5 $RUN scripts/CITY_eval4_sigma.py --sigma 0.3 --light RL-H:$k --fleet L-ACT:0 --guard always --seeds $TS $SM --record $N/traces/rlh${k}_s{seed}.npz --tag fit_RLH$k --out $N/traces >> $N/traces/run.log 2>&1 & done; wait
for k in $LT; do F=""; for s in $TS; do F="$F $N/traces/rlh${k}_s$s.npz"; done; $RUN scripts/CITY_spat_forecast.py fit $k $N/m2b/forecast_rlh$k.json $F || { echo "open-loop fit FAIL t$k"; exit 1; }; done
for k in $LT; do [ -f $N/prep/prov_rlh${k}_cl.json ] || nice -n 5 $PY -u scripts/CITY_n3_prep.py $k $N/prep > $N/prep/prep_k$k.out 2>&1 & done; wait
NF=8; [ "${SMOKE:-0}" = 1 ] && NF=1
for k in $LT; do $PY -c "
import json; T = json.load(open('$N/prep/prov_rlh${k}_cl.json')); assert len(T['per']) == 20 and T['n_files'] == $NF, (len(T['per']), T['n_files']); print('KN3-3 t$k: 20 lights x', T['n_files'], 'files')" || { echo "KN3-3 FAIL t$k"; exit 1; }; done
J=$N/collect_jobs.txt; : > $J; for k in $LT; do for s in $TS; do echo "$k $s" >> $J; done; done
export DEV; xargs -P 8 -L 1 bash -c '[ -f $N/cdata/c2_t$0/feat_s$1.npz ] || nice -n 5 $RUN scripts/CITY_n2_collect.py --featlog $N/cdata/c2_t$0 --spat-arm fc2:0.1:$N/prep/prov_rlh$0_cl.json --light RL-H:$0 --fleet PL:$DEV --seeds $1 $SM --tag C_t$0_s$1 --out $N/cdata/c2_t$0 >> $N/cdata/run.log 2>&1 || { echo "FAIL collect $0 $1"; exit 255; }' < $J || { echo "collection failure: stop"; exit 1; }
for k in $LT; do [ -f $N/cmodel/n2_k$k.pt ] || $RUN scripts/CITY_n2_fit.py $k $N/cdata/c2_t$k $N/cmodel > $N/cmodel/fit_t$k.log 2>&1 || { echo "FIT FAIL t$k"; exit 1; }; done
K1=$(echo $LT | cut -d' ' -f1); F1=$(echo $FS | cut -d' ' -f1); K=$N/check/kf2_t$K1; mkdir -p $K
$RUN scripts/CITY_eval_n2.py --n2 0.5:$N/cmodel/n2_k$K1.pt --featlog $K --light RL-H:$K1 --fleet PL:$N/fleets/N3_s${F1}_fleet.pt --seeds 0 --smoke --tag KF2_n2 --out $K > $K/run.log 2>&1 || { echo "KF-2 run FAIL"; exit 1; }
$RUN scripts/CITY_n2_parity.py $K 0 $N/cmodel/n2_k$K1.pt | tee $N/check/kf2.txt || { echo "KF-2 FAIL: stop"; exit 1; }
J=$N/tune_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$DEV"; echo "R_t$k scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  for ab in "1 0" "1.5 0" "2 0" "1 0.25" "1.5 0.25" "2 0.25" "1 0.5" "1.5 0.5" "2 0.5" "3 0.5"; do set -- $ab; T=$(echo "T_t${k}_a$1_b$2" | tr '.' 'p')
    echo "$T scripts/CITY_eval_n4.py --n4 0.5:hyb:$N/prep/prov_rlh${k}_cl.json:$N/cmodel/n2_k$k.pt $F --light-obs q:$1:$2" >> $J; done; done
export SS="$TUNES"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $N/tune/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $N/tune >> $N/tune/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "tuning failure: stop"; exit 1; }
$PY scripts/CITY_w7_tune.py $N $LT | tee $N/tune/tune.txt || { echo "TUNE FAIL"; exit 1; }
# 4. confirmation on fresh rand3 traffic
J=$N/conf_jobs.txt; : > $J
for k in $LT; do AB=$($PY -c "import json;print(json.load(open('$N/tune/choice.json'))['$k']['choice'].replace(',',':'))"); N4="--n4 0.5:hyb:$N/prep/prov_rlh${k}_cl.json:$N/cmodel/n2_k$k.pt"
  for s in $FS; do F="--light RL-H:$k --fleet PL:$N/fleets/N3_s${s}_fleet.pt"
    echo "R_t${k}_s$s scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "TSI_t${k}_s$s scripts/CITY_eval_n4.py $N4 $F --light-obs q:$AB" >> $J
    echo "HYB_t${k}_s$s scripts/CITY_eval_n4.py $N4 $F" >> $J; echo "ADP_t${k}_s$s scripts/CITY_eval_f1.py --spat-arm none $F --light-obs q:$AB" >> $J; done; done
export SS="$CS"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $N/conf/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $N/conf >> $N/conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation failure: stop"; exit 1; }
echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W8_SMOKE=$(dirname $N) W8_SEED=660 W8_DEV=600 $PY scripts/CITY_w8_report.py net3; else $PY scripts/CITY_w8_report.py net3; fi || exit 1; echo "W8-NET3 done $(date)"
