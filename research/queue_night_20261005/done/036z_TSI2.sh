#!/usr/bin/env bash
# TSI-2 (PROTOCOL_CITY_TSI2_20261005): seeds 660-663 + 720-739 -> per-light tuning (55 jobs) -> choice -> confirmation (100 jobs) -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/tsi2_20261005; mkdir -p $D/check $D/tune $D/conf; export XPLAY_TMP=$PWD/$D/check
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P=research/city_sim/spat_pilot_20261004/fleets_v11; TB=research/city_sim/f1b_20261004/prep
MOD=research/city_sim/tsi_20261005/cmodel/c2; FB=research/city_sim/f1b_20261004/train; RUN="$PY -u scripts/CITY_f1a1_run.py"; echo "TSI2 start $(date)"
gen() { F=$1; shift; if [ ! -f $G/$F ]; then for s in "$@"; do [ -f $G/rou_s$s.xml ] && { echo "KT2-0 FAIL: rou_s$s existed"; exit 1; }; done
  for s in "$@"; do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; date > $G/$F; fi; }
gen TUNE660_generated 660 661 662 663; gen CONF720_generated $(seq 720 739); echo "seeds ready $(date)"
J=$D/tune_jobs.txt; : > $J
for t in 4 5 6 7 8; do F="--light RL-H:$t --fleet PL:$P/L11_s13_fleet.pt"; echo "R_t$t scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  for ab in "1 0" "1.5 0" "2 0" "1 0.25" "1.5 0.25" "2 0.25" "1 0.5" "1.5 0.5" "2 0.5" "3 0.5"; do set -- $ab; T=$(echo "T_t${t}_a$1_b$2" | tr '.' 'p')
    echo "$T scripts/CITY_eval_n4.py --n4 0.5:hyb:$TB/prov_rlh${t}_cl.json:$MOD/n2_k$t.pt $F --light-obs q:$1:$2" >> $J; done; done
export PY D RUN; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/tune/$T.json ] || nice -n 5 $RUN "$@" --seeds 660 661 662 663 --tag $T --out $D/tune >> $D/tune/run.log 2>&1 || echo "FAIL $T"' < $J
$PY scripts/CITY_tsi2_tune.py | tee $D/tune/tune.txt || { echo "TUNE FAIL"; exit 1; }
J=$D/conf_jobs.txt; : > $J; FLS=(s213 s313 s413 s513); F1=(F1B_s213_t4 F1B_s313_t5 F1B_s413_t6 F1B_s513_t7)
for t in 4 5 6 7 8; do AB=$($PY -c "import json;print(json.load(open('$D/tune/choice.json'))['$t']['choice'].replace(',',':'))"); N4="--n4 0.5:hyb:$TB/prov_rlh${t}_cl.json:$MOD/n2_k$t.pt"
  for i in 0 1 2 3; do fl=${FLS[$i]}; F="--light RL-H:$t --fleet PL:$P/L11_${fl}_fleet.pt"
    echo "R_t${t}_${fl} scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "TSI2_t${t}_${fl} scripts/CITY_eval_n4.py $N4 $F --light-obs q:$AB" >> $J
    echo "HYB_t${t}_${fl} scripts/CITY_eval_n4.py $N4 $F" >> $J; echo "ADP2_t${t}_${fl} scripts/CITY_eval_f1.py --spat-arm none $F --light-obs q:$AB" >> $J
    echo "F1B_t${t}_${F1[$i]} scripts/CITY_eval_f1b.py --spat-arm fc2:0.1:$TB/prov_rlh${t}_cl.json --light RL-H:$t --fleet PL:$FB/${F1[$i]}_fleet.pt" >> $J; done; done
export SS="$(seq -s ' ' 720 739)"; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || echo "FAIL $T"' < $J
echo "panel done $(date)"; $PY scripts/CITY_tsi2_report.py; echo "TSI2 done $(date)"
