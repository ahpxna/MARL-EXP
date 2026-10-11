#!/usr/bin/env bash
# MT-A4/A5 job (PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010): train arm lg for k = 59..63 (5 lanes, teleports off), then test days 0-4 (teleports 300).
set -u; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=osm
PY=external_envs/city_runtime/bin/python; OUT=research/city_sim/midtown_transfer_20261010/retrain/moe_lg; E5=research/city_sim/midtown_transfer_20261010/eval5; mkdir -p $OUT
echo "train start $(date)"
for k in 59 60 61 62 63; do
  ( MT_TTT=-1 MT_LIGHT_INDEX=1 nice -n 5 $PY -u scripts/DEMO_midtown.py scripts/CITY_mt_train_light_moe.py --arm lg --k $k --out $OUT > $OUT/train_t$k.log 2>&1 ) &
done; wait
for k in 59 60 61 62 63; do test -f $OUT/RL-H_t$k.pt || { echo "MISSING checkpoint t$k"; tail -3 $OUT/train_t$k.log; exit 1; }; done
echo "test start $(date)"
for k in 59 60 61 62 63; do
  ( W19_LIGHTS=$OUT MT_LIGHT_INDEX=1 nice -n 5 $PY -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py scripts/CITY_eval6_v11.py --light RL-H:$k --fleet L-ACT:0 --guard always --seeds 0 1 2 3 4 --tag MTR_A5lg_t$k --out $E5 > $E5/MTR_A5lg_t$k.log 2>&1 ) &
done; wait
for k in 59 60 61 62 63; do grep -q '"status": "COMPLETE"' $E5/MTR_A5lg_t$k.json 2>/dev/null || { echo "INCOMPLETE MTR_A5lg_t$k"; exit 1; }; done
$PY scripts/MT_report.py; echo "job done $(date)"
