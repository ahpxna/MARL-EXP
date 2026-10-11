#!/usr/bin/env bash
# GEN (PROTOCOL_CITY_GEN_20261005): traffic 750-759 -> (a) R8 / R9, (b) c2 ablation, (c) penetration, (d) H-PATH -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/gen_20261005; mkdir -p $D/check $D/conf; export XPLAY_TMP=$PWD/$D/check
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P=research/city_sim/spat_pilot_20261004/fleets_v11; TB=research/city_sim/f1b_20261004/prep
MOD=research/city_sim/tsi_20261005/cmodel/c2; CH=research/city_sim/tsi2_20261005/tune/choice.json; FB=research/city_sim/f1b_20261004/train; RULE=research/city_sim/f1_20261004/train/RULE0_fleet.pt; TH=research/city_sim/spat_pilot_20261004/lane_d
RUN="$PY -u scripts/CITY_f1a1_run.py"; echo "GEN start $(date)"; [ -f $CH ] || { echo "no TSI-2 choice"; exit 1; }
if [ ! -f $G/GEN750_generated ]; then for s in $(seq 750 759); do [ -f $G/rou_s$s.xml ] && { echo "KG-0 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 750 759); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; date > $G/GEN750_generated; fi
J=$D/jobs.txt; : > $J
for t in 4 5 6 7 8; do AB=$($PY -c "import json;print(json.load(open('$CH'))['$t']['choice'].replace(',',':'))"); N4="--n4 0.5:hyb:$TB/prov_rlh${t}_cl.json:$MOD/n2_k$t.pt"; L="--light RL-H:$t"
  for c in "rule R8 PL:$RULE" "r9 s2 ESLD:$TH/theta_s2.json" "r9 s3 ESLD:$TH/theta_s3.json"; do set -- $c
    echo "R_$1_t${t}_$2 $RUN scripts/CITY_eval_f1.py --spat-arm none $L --fleet $3" >> $J; echo "TSI2_$1_t${t}_$2 $RUN scripts/CITY_eval_n4.py $N4 $L --fleet $3 --light-obs q:$AB" >> $J
    echo "HYB_$1_t${t}_$2 $RUN scripts/CITY_eval_n4.py $N4 $L --fleet $3" >> $J; done
  for fl in s213 s313 s413 s513; do F="$L --fleet PL:$P/L11_${fl}_fleet.pt"
    echo "R_r10_t${t}_${fl} $RUN scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "TSI2_r10_t${t}_${fl} $RUN scripts/CITY_eval_n4.py $N4 $F --light-obs q:$AB" >> $J
    echo "C2Q_r10_t${t}_${fl} $RUN scripts/CITY_eval_f1b.py --spat-arm fc2:0.5:$TB/prov_rlh${t}_cl.json $F --light-obs q:$AB" >> $J; done
  for rho in 0.25 0.75; do for fl in s213 s313; do F="$L --fleet PL:$P/L11_${fl}_fleet.pt"; W="$PY -u scripts/CITY_rho_run.py $rho scripts/CITY_f1a1_run.py"
    echo "R_r10_t${t}_${fl}_rho$rho $W scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "TSI2_r10_t${t}_${fl}_rho$rho $W scripts/CITY_eval_n4.py $N4 $F --light-obs q:$AB" >> $J; done; done; done
for fl in s213 s313 s413 s513; do echo "FT_${fl} $PY -u scripts/CITY_eval_n8.py --spat program --light FT --fleet PL:$P/L11_${fl}_fleet.pt" >> $J; done
for f in F1B_s213_t4 F1B_s313_t5 F1B_s413_t6 F1B_s513_t7; do echo "FT_$f $PY -u scripts/CITY_eval_n8.py --spat program --light FT --fleet PL:$FB/${f}_fleet.pt" >> $J; done
export D SS="$(seq -s ' ' 750 759)"; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 "$@" --seeds $SS --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || echo "FAIL $T"' < $J
echo "panel done $(date)"; $PY scripts/CITY_gen_report.py; echo "GEN done $(date)"
