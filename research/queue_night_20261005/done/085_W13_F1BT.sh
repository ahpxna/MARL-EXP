#!/usr/bin/env bash
# W13-5 (PROTOCOL_CITY_WAVE13_20261006, Amendment A1): F1B-T fleets (scratch, 200 episodes, F1-B recipe) trained with the W8-2 TSI in force
# (fleet seed s(1013+100i) under light t(14+i), i = 0..3, as F1-B); fresh traffic 940-959 (generated after a non-existence check); arms R,
# TSI, F1B, F1BonT, F1BT x t14-t18 x s1013-s1313 x 20 under HBEFA4 and PHEMlight5 (modes wrapper); report D13-4.
# SMOKE=1: one fleet (s1013, t14), 2 episodes of 300 s, evaluation t14 x s1013 on existing traffic 860, 600 s, into W13_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W13_DIR:-research/city_sim/w13_20261006}; F2=research/city_sim/w8_20261005/fresh2; G=research/city_sim/demand/grid4
RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P5=em:PHEMlight5/PC_EU4_G
mkdir -p $D/f1bt $D/f1bt_conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd); echo "W13-F1BT start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; EP=2; TR="1013:14"; LT="14"; FS="1013"; CS="860"; else SM=""; EP=200; TR="1013:14 1113:15 1213:16 1313:17"; LT="14 15 16 17 18"; FS="1013 1113 1213 1313"; CS="$(seq -s ' ' 940 959)"; fi
AB() { $PY -c "import json;print(json.load(open('$F2/tune/choice.json'))['$1']['choice'].replace(',',':'))"; }
N4P() { echo "0.5:$F2/prep/prov_rlh$1_cl.json:$F2/cmodel/n2_k$1.pt"; }
# 1. training (parallel, one process per fleet)
for x in $TR; do s=${x%%:*}; k=${x##*:}; [ -f $D/f1bt/F1BT_s${s}_t${k}_fleet.pt ] || W13_N4=$(N4P $k) W13_AB=$(AB $k) nice -n 5 $PY -u scripts/CITY_w13_train_f1bt.py \
  --seed $s --light-k $k --init scratch --table $F2/prep/prov_rlh${k}_cl.json --q 0.1 --episodes $EP $SM --name F1BT_s${s}_t$k --out $D/f1bt > $D/f1bt/F1BT_s${s}_t$k.out 2>&1 & done; wait
for x in $TR; do s=${x%%:*}; k=${x##*:}; [ -f $D/f1bt/F1BT_s${s}_t${k}_fleet.pt ] || { echo "training FAIL s$s t$k"; tail -3 $D/f1bt/F1BT_s${s}_t$k.out; exit 1; }; done; echo "training done $(date)"
# 2. fresh traffic 940-959
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF940_generated ]; then
  for s in $(seq 940 959); do [ -f $G/rou_s$s.xml ] && { echo "KW13-5 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 940 959); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF940_generated; echo "traffic 940-959 generated $(date)"; fi
# 3. evaluation (F1B / F1BT fleet of fleet seed s = the one trained under t(14+i), crossed over every light, as in W8-2)
J=$D/f1bt_jobs.txt; : > $J
for k in $LT; do N4="--n4 $(N4P $k | sed 's/^0.5:/0.5:hyb:/')"; A=$(AB $k)
  for s in $FS; do kk=$(( 14 + (s - 1013) / 100 )); F="--light RL-H:$k"; P="PL:$F2/fleets/L11_s${s}_fleet.pt"; PB="PL:$F2/f1b/F1B_s${s}_t${kk}_fleet.pt"; PT="PL:$D/f1bt/F1BT_s${s}_t${kk}_fleet.pt"
    for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
      echo "R${x}_t${k}_s$s $em scripts/CITY_eval_f1.py --spat-arm none $F --fleet $P" >> $J
      echo "TSI${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $N4 $F --fleet $P --light-obs q:$A" >> $J
      echo "F1B${x}_t${k}_s$s $em scripts/CITY_eval_f1b.py --spat-arm fc2:0.1:$F2/prep/prov_rlh${k}_cl.json $F --fleet $PB" >> $J
      echo "F1BonT${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $N4 $F --fleet $PB --light-obs q:$A" >> $J
      echo "F1BT${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $N4 $F --fleet $PT --light-obs q:$A" >> $J; done; done; done
export PY D SM; export SS="$CS"
xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $D/f1bt_conf/$T.json ] || nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $D/f1bt_conf >> $D/f1bt_conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "evaluation failure: stop"; exit 1; }
if [ "${SMOKE:-0}" = 1 ]; then W13_SMOKE=1 W13_SEED=860 $PY scripts/CITY_w13_f1bt_report.py $D; else $PY scripts/CITY_w13_f1bt_report.py $D; fi || { echo "report FAIL"; exit 1; }
echo "W13-F1BT done $(date)"
