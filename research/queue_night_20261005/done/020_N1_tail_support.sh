#!/usr/bin/env bash
# N1 (PROTOCOL_CITY_N1_TAIL_SUPPORT_20261005): DEV 600-611 generation -> KN1-1 -> grid4 16 jobs + spider 4 jobs (4 parallel) -> offline -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/n1_20261005; export XPLAY_TMP=$PWD/$D/check
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P=research/city_sim/spat_pilot_20261004/fleets_v11
TB=research/city_sim/m3_20261004/prep; SP=research/city_sim/m4_20261004/spider; echo "N1 start $(date)"
if [ ! -f research/city_sim/demand/grid4/DEV600_generated ]; then
  for s in $(seq 600 611); do [ -f $G/rou_s$s.xml ] && { echo "KN1-2 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 600 611); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 \
    --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; echo "600-611 generated $(date)" > $G/DEV600_generated; fi
$PY -u scripts/CITY_eval_n1.py --n1 all:0.1:$TB/prov_rlh0_cl.json --light RL-H:0 --fleet PL:$P/L11_s13_fleet.pt --seeds 600 --smoke --tag K_all --out $D/check > $D/check/k.log 2>&1 || exit 1
$PY -u scripts/CITY_eval_f1b.py --spat-arm fc2:0.1:$TB/prov_rlh0_cl.json --light RL-H:0 --fleet PL:$P/L11_s13_fleet.pt --seeds 600 --smoke --tag K_fc2 --out $D/check >> $D/check/k.log 2>&1 || exit 1
$PY -c "
import sys; sys.path.insert(0,'.')
from scripts.CITY_spatp_report import rows
C=rows('$D/check'); Q=('timeloss','timeloss_agent','timeloss_human','fuel_agent','fuel','teleports'); ok=all(C['K_all'][600][q]==C['K_fc2'][600][q] for q in Q)
print('KN1-1 all == c2:', ok); raise SystemExit(0 if ok else 1)" || { echo "KN1-1 FAIL"; exit 1; }
J=$D/jobs.txt; : > $J
for k in 0 1; do for fl in s13 s113; do echo "g4 R_k${k}_${fl} scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$k --fleet PL:$P/L11_${fl}_fleet.pt" >> $J
  for m in all tail strict; do echo "g4 N1${m}_k${k}_${fl} scripts/CITY_eval_n1.py --n1 $m:0.1:$TB/prov_rlh${k}_cl.json --light RL-H:$k --fleet PL:$P/L11_${fl}_fleet.pt" >> $J; done; done; done
for k in 11 111; do for m in tail strict; do echo "sp N1${m}_$k scripts/CITY_m4s_n1_eval.py --n1 $m:0.1:$SP/s3b/prov/fkcl_rlk$k.json --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J; done; done
export PY D; xargs -P 4 -L 1 bash -c 'O=$0; T=$1; shift 1; if [ $O = g4 ]; then SS="600 601 602 603 604 605 606 607 608 609 610 611"; else SS="100 101 102 103 104 105 106 107 108 109"; fi
  [ -f $D/$O/$T.json ] || nice -n 5 $PY -u "$@" --seeds $SS --tag $T --out $D/$O >> $D/$O/run.log 2>&1 || echo "FAIL $T"' < $J
echo "panel done $(date)"
for k in 0 1; do $PY scripts/CITY_n1_offline.py $TB/prov_rlh${k}_cl.json 0.1 grid4 $TB/prep_rlh${k}_s*.npz > $D/check/offline_g4_k$k.json; done
for k in 11 111; do $PY scripts/CITY_n1_offline.py $SP/s3b/prov/fkcl_rlk$k.json 0.1 spider $SP/s3b/traces/cl_rlk${k}_s*.npz > $D/check/offline_sp_$k.json; done
$PY scripts/CITY_n1_report.py; echo "N1 done $(date)"
