#!/usr/bin/env bash
# SHIFT (PROTOCOL_CITY_SHIFT_20261005): traffic 740-749 at period 1.6 -> 60 jobs -> report.  Needs tsi2 tune choice.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/shift_20261005; export XPLAY_TMP=$PWD/$D/check
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P=research/city_sim/spat_pilot_20261004/fleets_v11; TB=research/city_sim/f1b_20261004/prep
MOD=research/city_sim/tsi_20261005/cmodel/c2; CH=research/city_sim/tsi2_20261005/tune/choice.json; RUN="$PY -u scripts/CITY_f1a1_run.py"; echo "SHIFT start $(date)"
[ -f $CH ] || { echo "no TSI-2 choice"; exit 1; }
if [ ! -f $G/SHIFT740_p16_generated ]; then for s in $(seq 740 749); do [ -f $G/rou_s$s.xml ] && { echo "KS-0 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 740 749); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 1.6 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; echo "period 1.6 $(date)" > $G/SHIFT740_p16_generated; fi
J=$D/jobs.txt; : > $J
for t in 4 5 6 7 8; do AB=$($PY -c "import json;print(json.load(open('$CH'))['$t']['choice'].replace(',',':'))"); N4="--n4 0.5:hyb:$TB/prov_rlh${t}_cl.json:$MOD/n2_k$t.pt"
  for fl in s213 s313 s413 s513; do F="--light RL-H:$t --fleet PL:$P/L11_${fl}_fleet.pt"
    echo "R_t${t}_${fl} scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "TSI2_t${t}_${fl} scripts/CITY_eval_n4.py $N4 $F --light-obs q:$AB" >> $J; echo "HYB_t${t}_${fl} scripts/CITY_eval_n4.py $N4 $F" >> $J; done; done
export PY D RUN SS="$(seq -s ' ' 740 749)"; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || echo "FAIL $T"' < $J
$PY scripts/CITY_shift_report.py; echo "SHIFT done $(date)"
