#!/usr/bin/env bash
# F1-2 (PROTOCOL_CITY_F1_SALTLAKE_20261008 + A1-A4): 400S & 200W only (RLW passed G1 there, C-210).  R10-recipe PPO fleets, seeds 13 / 113,
# 400 episodes, tuned FT with exact FT SPaT, TRAIN days in rotation (CITY_sl_run); M1-SL on the 10 DEV days: OFF vs PL x HBEFA4 / PHEMlight5.
# SMOKE=1: seed 13, 1 episode, first DEV day, into SL_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 SL_SITE=400sX200w; PY=external_envs/city_runtime/bin/python
D=${SL_DIR:-research/city_sim/f1_saltlake}/m1; mkdir -p $D/fleets; P5=em:PHEMlight5/PC_EU4_G; echo "F1-SL-M1 start $(date)"
DV="$($PY -c "import sys; sys.path.insert(0,'.'); from scripts.CITY_sl_build import days; print(' '.join(str(d.timetuple().tm_yday) for d in days('400sX200w','dev')))")"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; FS="13"; FEP=1; DV="$(echo $DV | cut -d' ' -f1)"; else SM=""; FS="13 113"; FEP=400; fi
for s in $FS; do [ -f $D/fleets/L11_sl_s${s}_fleet.pt ] || nice -n 5 $PY -u scripts/CITY_sl_run.py scripts/CITY_fleet_train_v11_ppo.py --spat on --seed $s --episodes $FEP --name L11_sl_s$s --out $D/fleets --resume $SM > $D/fleets/L11_sl_s$s.out 2>&1 & done; wait
for s in $FS; do [ -f $D/fleets/L11_sl_s${s}_fleet.pt ] || { echo "missing fleet $s: stop"; tail -3 $D/fleets/L11_sl_s$s.out; exit 1; }; done
J=$D/m1_jobs.txt; : > $J
for x in "" P5; do M=none; [ -z "$x" ] || M=$P5
  echo "OFF${x}_t0_h $M scripts/CITY_eval6_v11.py --light FT --fleet L-ACT:0 --guard always" >> $J
  for s in $FS; do echo "PL${x}_t0_s$s $M scripts/CITY_eval6_v11.py --light FT --fleet PL:$D/fleets/L11_sl_s${s}_fleet.pt" >> $J; done; done
export PY SM OUT=$D SS="$DV"
xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $OUT/$T.json ] && exit 0
  nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_sl_runw.py scripts/CITY_w13_modes.py "$@" --seeds $SS --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "rows failure: stop"; exit 1; }
SL_SMOKE=${SMOKE:-0} $PY scripts/CITY_sl_m1_report.py $D || { echo "report FAIL"; exit 1; }
echo "F1-SL-M1 done $(date)"
