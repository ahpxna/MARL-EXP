#!/usr/bin/env bash
# W9-6 MP (PROTOCOL_CITY_WAVE9_20261005): MaxPressure (CITY_eval4.MaxPressure, unchanged) as the upgraded signal on grid4.  Fleet-side service
# for MP with the TSI fleet-side pipeline: sigma* traces (TRAIN 0-7) -> open-loop table -> closed-loop table (dev fleet L11_s13 on c2 q 0.5,
# recorded, refitted) -> N2 logs (dev fleet on c2 q 0.1) -> N2 fit -> KF-2 parity; fresh traffic 820-839; arms R_FT, PL_FT, R_MP, NAIVE_MP,
# C2_MP, HYB_MP x W7-1 fleets s613-s913 x 20; report.  SMOKE=1: one fleet, TRAIN 0-7 at 300 s, seed 820, 600 s, into W9_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W9_DIR:-research/city_sim/w9_20261005/mp}; mkdir -p $D/traces $D/m2b $D/prep $D/cdata $D/cmodel $D/check $D/conf; export XPLAY_TMP=$(cd $D/check && pwd)
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; W7=research/city_sim/w7_20261005/fpr
DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt; RUN="$PY -u scripts/CITY_w9_run.py none"; echo "W9-MP start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; FS="613"; TS="0 1 2 3 4 5 6 7"; CS="820"; else SM=""; FS="613 713 813 913"; TS="0 1 2 3 4 5 6 7"; CS="$(seq -s ' ' 820 839)"; fi
# 1. sigma* traces under MP and the open-loop table
[ -f $D/traces/fit_MP.json ] || $RUN scripts/CITY_eval4_sigma.py --sigma 0.3 --light MP --fleet L-ACT:0 --guard always --seeds $TS $SM --record $D/traces/mp_s{seed}.npz --tag fit_MP --out $D/traces > $D/traces/run.log 2>&1 || { echo "trace FAIL"; exit 1; }
F=""; for s in $TS; do F="$F $D/traces/mp_s$s.npz"; done; $RUN scripts/CITY_spat_forecast.py fit MP $D/m2b/forecast_mp.json $F || { echo "open-loop fit FAIL"; exit 1; }
# 2. closed-loop table: dev fleet on c2 q 0.5 of the open-loop table, recorded, refitted
[ -f $D/prep/PREP_MP.json ] || $RUN scripts/CITY_eval_f1b.py --spat-arm fc2:0.5:$D/m2b/forecast_mp.json --light MP --fleet PL:$DEV --seeds $TS $SM --record $D/prep/prep_mp_s{seed}.npz --tag PREP_MP --out $D/prep > $D/prep/run.log 2>&1 || { echo "prep FAIL"; exit 1; }
F=""; for s in $TS; do F="$F $D/prep/prep_mp_s$s.npz"; done; $RUN scripts/CITY_spat_forecast.py fit MP $D/prep/prov_mp_cl.json $F || { echo "closed-loop fit FAIL"; exit 1; }
$PY -c "
import json; T = json.load(open('$D/prep/prov_mp_cl.json')); assert len(T['per']) == 16, len(T['per']); print('KM-3: 16 lights x', T['n_files'], 'files')" || { echo "KM-3 FAIL"; exit 1; }
# 3. N2 logs and fit
J=$D/collect_jobs.txt; : > $J; for s in $TS; do echo "$s" >> $J; done; export PY D RUN SM DEV
xargs -P 8 -L 1 bash -c '[ -f $D/cdata/c2_mp/feat_s$0.npz ] || nice -n 5 $RUN scripts/CITY_n2_collect.py --featlog $D/cdata/c2_mp --spat-arm fc2:0.1:$D/prep/prov_mp_cl.json --light MP --fleet PL:$DEV --seeds $0 $SM --tag C_mp_s$0 --out $D/cdata/c2_mp >> $D/cdata/run.log 2>&1 || { echo "FAIL collect $0"; exit 255; }' < $J || { echo "collection failure: stop"; exit 1; }
[ -f $D/cmodel/n2_kMP.pt ] || $PY -u scripts/CITY_n2_fit.py MP $D/cdata/c2_mp $D/cmodel > $D/cmodel/fit_mp.log 2>&1 || { echo "FIT FAIL"; tail -5 $D/cmodel/fit_mp.log; exit 1; }
F1=$(echo $FS | cut -d' ' -f1); K=$D/check/kf2_mp; mkdir -p $K
$RUN scripts/CITY_eval_n2.py --n2 0.5:$D/cmodel/n2_kMP.pt --featlog $K --light MP --fleet PL:$W7/fleets/L11_s${F1}_fleet.pt --seeds 0 --smoke --tag KF2_n2 --out $K > $K/run.log 2>&1 || { echo "KF-2 run FAIL"; exit 1; }
$PY scripts/CITY_n2_parity.py $K 0 $D/cmodel/n2_kMP.pt | tee $D/check/kf2.txt || { echo "KF-2 FAIL: stop"; exit 1; }
# 4. fresh confirmation traffic 820-839 (not in smoke)
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF820_generated ]; then for s in $(seq 820 839); do [ -f $G/rou_s$s.xml ] && { echo "KW-0 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 820 839); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; date > $G/CONF820_generated; fi
[ "${SMOKE:-0}" = 1 ] && [ ! -f $G/rou_s820.xml ] && { echo "smoke uses TRAIN seed 0 traffic as 820 is not generated yet"; CS="0"; }
# 5. confirmation
J=$D/conf_jobs.txt; : > $J; N4="--n4 0.5:hyb:$D/prep/prov_mp_cl.json:$D/cmodel/n2_kMP.pt"
for s in $FS; do P="PL:$W7/fleets/L11_s${s}_fleet.pt"
  echo "R_FT_s$s scripts/CITY_eval_f1.py --spat-arm none --light FT --fleet $P" >> $J; echo "PL_FT_s$s scripts/CITY_eval6_v11.py --light FT --fleet $P" >> $J
  echo "R_MP_s$s scripts/CITY_eval_f1.py --spat-arm none --light MP --fleet $P" >> $J; echo "NAIVE_MP_s$s scripts/CITY_eval6_v11.py --light MP --fleet $P" >> $J
  echo "C2_MP_s$s scripts/CITY_eval_f1b.py --spat-arm fc2:0.5:$D/prep/prov_mp_cl.json --light MP --fleet $P" >> $J
  echo "HYB_MP_s$s scripts/CITY_eval_n4.py $N4 --light MP --fleet $P" >> $J; done
export SS="$CS"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation failure: stop"; exit 1; }
echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W9_SMOKE=$(dirname $D) W9_SEED=$CS $PY scripts/CITY_w9_report.py mp; else $PY scripts/CITY_w9_report.py mp; fi || exit 1; echo "W9-MP done $(date)"
