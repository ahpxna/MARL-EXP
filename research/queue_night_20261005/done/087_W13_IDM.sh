#!/usr/bin/env bash
# W13-6a (PROTOCOL_CITY_WAVE13_20261006, Amendment A1): TSI recalibrated under IDM, every policy frozen (FRESH2 lights t14-t18, frozen fleets,
# development fleet L11_s13), with the FRESH2 recipe and seeds: traces (TRAIN 0-7) -> open-loop tables -> closed-loop c2 prep (KF-3) -> N2 logs
# -> fit -> KF-2 parity -> adapter grid on TUNE 660-663 with the TSI-2 rule (CITY_w7_tune) -> fresh traffic 960-979 (non-existence check) ->
# R, TSIK, TSII, F1B x t14-t18 x s1013-s1313 x 20 under IDM, HBEFA4 and PHEMlight5 -> report D13-5.  Every simulation via CITY_w13_idm.py.
# SMOKE=1: t14, short budgets (600 s / 300 s prep), TUNE 660, conf t14 x s1013 x 860, into W13_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W13_DIR:-research/city_sim/w13_20261006}; I=$D/idm; F2=research/city_sim/w8_20261005/fresh2; DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; IR="$PY -u scripts/CITY_w13_idm.py"
mkdir -p $I/traces $I/m2b $I/prep $I/cdata $I/cmodel $I/check $I/tune $I/conf; export XPLAY_TMP=$(cd $I/check && pwd) W7_FPR_DIR=$(cd $I && pwd); echo "W13-IDM start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="14"; TS="0 1 2 3 4 5 6 7"; TUNES="660"; FS="1013"; CS="860"; NF=1; export W7_TUNE_SEEDS=660 W7_PREP_N=1 W7_PREP_END=300
else SM=""; LT="14 15 16 17 18"; TS="0 1 2 3 4 5 6 7"; TUNES="660 661 662 663"; FS="1013 1113 1213 1313"; CS="$(seq -s ' ' 960 979)"; NF=8; fi
# 1-2. traces and open-loop tables under IDM
for k in $LT; do [ -f $I/traces/fit_RLH$k.json ] || nice -n 5 $IR scripts/CITY_eval4_sigma.py --sigma 0.3 --light RL-H:$k --fleet L-ACT:0 --guard always --seeds $TS $SM --record $I/traces/rlh${k}_s{seed}.npz --tag fit_RLH$k --out $I/traces >> $I/traces/run.log 2>&1 & done; wait
for k in $LT; do F=""; for s in $TS; do F="$F $I/traces/rlh${k}_s$s.npz"; done; $IR scripts/CITY_spat_forecast.py fit $k $I/m2b/forecast_rlh$k.json $F > $I/m2b/fit_t$k.log 2>&1 || { echo "open-loop fit FAIL t$k"; tail -3 $I/m2b/fit_t$k.log; exit 1; }; done
# 3. closed-loop c2 prep under IDM (CE.run_episode patched by CITY_w13_idm) + KF-3
for k in $LT; do [ -f $I/prep/prov_rlh${k}_cl.json ] || nice -n 5 $IR scripts/CITY_w8_prep.py $k $I/prep > $I/prep/prep_k$k.out 2>&1 & done; wait
for k in $LT; do $PY -c "
import json; T = json.load(open('$I/prep/prov_rlh${k}_cl.json')); assert len(T['per']) == 16 and T['n_files'] == $NF, (len(T['per']), T['n_files']); print('KF-3 t$k ok')" || { echo "KF-3 FAIL t$k"; exit 1; }; done
grep -h "KI-0" $I/prep/prep_k*.out | head -2
# 4-5. N2 logs and fits, KF-2
J=$I/collect_jobs.txt; : > $J; for k in $LT; do for s in $TS; do echo "$k $s" >> $J; done; done
export PY I SM DEV IR; xargs -P 6 -L 1 bash -c '[ -f $I/cdata/c2_t$0/feat_s$1.npz ] || nice -n 5 $IR scripts/CITY_n2_collect.py --featlog $I/cdata/c2_t$0 --spat-arm fc2:0.1:$I/prep/prov_rlh$0_cl.json --light RL-H:$0 --fleet PL:$DEV --seeds $1 $SM --tag C_t$0_s$1 --out $I/cdata/c2_t$0 >> $I/cdata/run.log 2>&1 || { echo "FAIL collect $0 $1"; exit 255; }' < $J || { echo "collection failure: stop"; exit 1; }
for k in $LT; do [ -f $I/cmodel/n2_k$k.pt ] || $PY -u scripts/CITY_n2_fit.py $k $I/cdata/c2_t$k $I/cmodel > $I/cmodel/fit_t$k.log 2>&1 || { echo "FIT FAIL t$k"; exit 1; }; done
K1=$(echo $LT | cut -d' ' -f1); K=$I/check/kf2_t$K1; mkdir -p $K
$IR scripts/CITY_eval_n2.py --n2 0.5:$I/cmodel/n2_k$K1.pt --featlog $K --light RL-H:$K1 --fleet PL:$F2/fleets/L11_s1013_fleet.pt --seeds 0 --smoke --tag KF2_n2 --out $K > $K/run.log 2>&1 || { echo "KF-2 run FAIL"; exit 1; }
$PY scripts/CITY_n2_parity.py $K 0 $I/cmodel/n2_k$K1.pt | tee $I/check/kf2.txt || { echo "KF-2 FAIL: stop"; exit 1; }
# 6. adapter grid (TSI-2 rule) under IDM
J=$I/tune_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$DEV"; echo "R_t$k scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  for ab in "1 0" "1.5 0" "2 0" "1 0.25" "1.5 0.25" "2 0.25" "1 0.5" "1.5 0.5" "2 0.5" "3 0.5"; do set -- $ab; T=$(echo "T_t${k}_a$1_b$2" | tr '.' 'p')
    echo "$T scripts/CITY_eval_n4.py --n4 0.5:hyb:$I/prep/prov_rlh${k}_cl.json:$I/cmodel/n2_k$k.pt $F --light-obs q:$1:$2" >> $J; done; done
export SS="$TUNES"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $I/tune/$T.json ] || nice -n 5 $IR "$@" --seeds $SS $SM --tag $T --out $I/tune >> $I/tune/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "tuning failure: stop"; exit 1; }
$PY scripts/CITY_w7_tune.py $I $LT | tee $I/tune/tune.txt || { echo "tune selection FAIL"; exit 1; }
# 7. fresh traffic 960-979 and confirmation under IDM
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF960_generated ]; then
  for s in $(seq 960 979); do [ -f $G/rou_s$s.xml ] && { echo "KW13-6 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 960 979); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF960_generated; echo "traffic 960-979 generated $(date)"; fi
J=$I/conf_jobs.txt; : > $J
for k in $LT; do AK=$($PY -c "import json;print(json.load(open('$F2/tune/choice.json'))['$k']['choice'].replace(',',':'))"); AI=$($PY -c "import json;print(json.load(open('$I/tune/choice.json'))['$k']['choice'].replace(',',':'))")
  for s in $FS; do F="--light RL-H:$k --fleet PL:$F2/fleets/L11_s${s}_fleet.pt"; F1B=$(grep "^F1B_t${k}_s$s " $F2/conf_jobs.txt | cut -d' ' -f2-)
    for X in H4 P5; do x=""; [ "$X" = P5 ] && x=P5
      echo "R${x}_t${k}_s$s $X scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
      echo "TSIK${x}_t${k}_s$s $X scripts/CITY_eval_n4.py --n4 0.5:hyb:$F2/prep/prov_rlh${k}_cl.json:$F2/cmodel/n2_k$k.pt $F --light-obs q:$AK" >> $J
      echo "TSII${x}_t${k}_s$s $X scripts/CITY_eval_n4.py --n4 0.5:hyb:$I/prep/prov_rlh${k}_cl.json:$I/cmodel/n2_k$k.pt $F --light-obs q:$AI" >> $J
      echo "F1B${x}_t${k}_s$s $X $F1B" >> $J; done; done; done
export SS="$CS"
xargs -P 6 -L 1 bash -c 'T=$0; X=$1; shift; [ -f $I/conf/$T.json ] && exit 0; if [ "$X" = P5 ]; then export W13_EM=PHEMlight5/PC_EU4_G; fi; nice -n 5 $IR scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $I/conf >> $I/conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation failure: stop"; exit 1; }
if [ "${SMOKE:-0}" = 1 ]; then W13_SMOKE=1 W13_SEED=860 $PY scripts/CITY_w13_idm_report.py $D; else $PY scripts/CITY_w13_idm_report.py $D; fi || { echo "report FAIL"; exit 1; }
echo "W13-IDM done $(date)"
