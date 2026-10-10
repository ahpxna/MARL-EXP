#!/usr/bin/env bash
# TSI CONFIRMATION (PROTOCOL_CITY_TSI_20261005): traffic 700-719 -> per-light pipeline t4..t8 (TRAIN) -> KT checks -> 80 eval jobs -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/tsi_20261005; export XPLAY_TMP=$PWD/$D/check
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P=research/city_sim/spat_pilot_20261004/fleets_v11; TB=research/city_sim/f1b_20261004/prep
RUN="$PY -u scripts/CITY_f1a1_run.py"; echo "TSI-CONFIRM start $(date)"
[ -f $D/sel/choice.json ] && [ -f $D/sel/variant.json ] || { echo "no TSI choice / variant"; exit 1; }
AB=$($PY -c "import json;print(json.load(open('$D/sel/choice.json'))['choice'].replace(',',' '))"); set -- $AB; A=$1; B=$2; VAR=$($PY -c "import json;print(json.load(open('$D/sel/variant.json'))['variant'])"); echo "A* $A B* $B variant $VAR"
if [ ! -f $G/CONF700_generated ]; then
  for s in $(seq 700 719); do [ -f $G/rou_s$s.xml ] && { echo "KT-0 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 700 719); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 \
    --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; echo "700-719 generated $(date)" > $G/CONF700_generated; fi
J=$D/conf_collect.txt; : > $J; for t in 4 5 6 7 8; do for s in 0 1 2 3 4 5 6 7; do echo "$t $s" >> $J; done; done
export PY D P TB RUN A B; xargs -P 4 -L 1 bash -c '[ -f $D/cdata/c2_t$0/feat_s$1.npz ] || nice -n 5 $RUN scripts/CITY_n2_collect.py --featlog $D/cdata/c2_t$0 --spat-arm fc2:0.1:$TB/prov_rlh$0_cl.json --light RL-H:$0 --fleet PL:$P/L11_s13_fleet.pt --seeds $1 --tag C_t$0_s$1 --out $D/cdata/c2_t$0 >> $D/cdata/run.log 2>&1 || echo "FAIL c2 collect $0 $1"' < $J
for t in 4 5 6 7 8; do [ "$(ls $D/cdata/c2_t$t/feat_s*.npz 2>/dev/null | wc -l)" -eq 8 ] || { echo "c2 collection incomplete t$t"; exit 1; }; done; echo "c2 collected $(date)"
printf "4\n5\n6\n7\n8\n" | xargs -P 4 -I{} bash -c '$PY -u scripts/CITY_n2_fit.py {} $D/cdata/c2_t{} $D/cmodel/c2 > $D/cmodel/fit_c2_t{}.log 2>&1 || echo "FAIL fit c2 {}"'
MOD=$D/cmodel/c2
if [ "$VAR" = refit ]; then
  xargs -P 4 -L 1 bash -c '[ -f $D/cdata/tsi_t$0/feat_s$1.npz ] || nice -n 5 $RUN scripts/CITY_eval_n4f.py --n4 0.5:hyb:$TB/prov_rlh$0_cl.json:$D/cmodel/c2/n2_k$0.pt --featlog $D/cdata/tsi_t$0 --light RL-H:$0 --fleet PL:$P/L11_s13_fleet.pt --light-obs q:$A:$B --seeds $1 --tag C_t$0_s$1 --out $D/cdata/tsi_t$0 >> $D/cdata/run.log 2>&1 || echo "FAIL tsi collect $0 $1"' < $J
  for t in 4 5 6 7 8; do [ "$(ls $D/cdata/tsi_t$t/feat_s*.npz 2>/dev/null | wc -l)" -eq 8 ] || { echo "tsi collection incomplete t$t"; exit 1; }; done
  printf "4\n5\n6\n7\n8\n" | xargs -P 4 -I{} bash -c '$PY -u scripts/CITY_n2_fit.py {} $D/cdata/tsi_t{} $D/cmodel/refit > $D/cmodel/fit_refit_t{}.log 2>&1 || echo "FAIL fit refit {}"'; MOD=$D/cmodel/refit; fi
for t in 4 5 6 7 8; do [ -f $MOD/n2_k$t.pt ] || { echo "model missing t$t"; exit 1; }; done; echo "models ready $MOD $(date)"
$RUN scripts/CITY_eval_n4.py --n4 0.5:hyb:$TB/prov_rlh4_cl.json:$MOD/n2_k4.pt --light RL-H:4 --fleet PL:$P/L11_s213_fleet.pt --light-obs q:$A:$B --seeds 0 --smoke --tag KT --out $D/check > $D/check/kt.log 2>&1 || { echo "KT smoke FAIL"; tail -5 $D/check/kt.log; exit 1; }
$PY -c "import json;x=json.load(open('$D/check/KT_n4.json'));print('KT-2 hybrid', x['hybrid'], 'of', x['valid']);raise SystemExit(0 if x['hybrid']>0 and x['valid']>0 else 1)" || { echo "KT-2 FAIL"; exit 1; }
J=$D/conf_jobs.txt; : > $J
for t in 4 5 6 7 8; do for fl in s213 s313 s413 s513; do F="--light RL-H:$t --fleet PL:$P/L11_${fl}_fleet.pt"; N4="--n4 0.5:hyb:$TB/prov_rlh${t}_cl.json:$MOD/n2_k$t.pt"
  echo "R_t${t}_${fl} scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "TSI_t${t}_${fl} scripts/CITY_eval_n4.py $N4 $F --light-obs q:$A:$B" >> $J
  echo "HYB_t${t}_${fl} scripts/CITY_eval_n4.py $N4 $F" >> $J; echo "ADP_t${t}_${fl} scripts/CITY_eval_f1.py --spat-arm none $F --light-obs q:$A:$B" >> $J; done; done
export SS="$(seq -s ' ' 700 719)"; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || echo "FAIL $T"' < $J
echo "panel done $(date)"; $PY scripts/CITY_tsi_confirm_report.py; echo "TSI-CONFIRM done $(date)"
