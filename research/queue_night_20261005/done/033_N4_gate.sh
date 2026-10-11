#!/usr/bin/env bash
# N4 (PROTOCOL_CITY_N4_SERVICE_GATE_20261005): SELECT 650-655 generation -> KN4-1 (all == N2) -> SELECT grid 34 jobs -> choice -> DEV 16 jobs -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/n4_20261005; export XPLAY_TMP=$PWD/$D/check
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P=research/city_sim/spat_pilot_20261004/fleets_v11; M=research/city_sim/n2_20261005/model
echo "N4 start $(date)"
if [ ! -f $G/SEL650_generated ]; then
  for s in $(seq 650 655); do [ -f $G/rou_s$s.xml ] && { echo "KN4-0 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 650 655); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 \
    --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; echo "650-655 generated $(date)" > $G/SEL650_generated; fi
$PY -u scripts/CITY_eval_n4.py --n4 0.5:all:$M/n2_k0.pt --light RL-H:0 --fleet PL:$P/L11_s13_fleet.pt --seeds 600 --smoke --tag K_n4 --out $D/check > $D/check/k.log 2>&1 || { echo "SMOKE FAIL n4"; tail -5 $D/check/k.log; exit 1; }
$PY -u scripts/CITY_eval_n2.py --n2 0.5:$M/n2_k0.pt --light RL-H:0 --fleet PL:$P/L11_s13_fleet.pt --seeds 600 --smoke --tag K_n2 --out $D/check >> $D/check/k.log 2>&1 || { echo "SMOKE FAIL n2"; exit 1; }
$PY -c "
import sys; sys.path.insert(0,'.')
from scripts.CITY_spatp_report import rows
C=rows('$D/check'); Q=('timeloss','timeloss_agent','timeloss_human','fuel_agent','fuel','teleports'); ok=all(C['K_n4'][600][q]==C['K_n2'][600][q] for q in Q)
print('KN4-1 all == N2:', ok); raise SystemExit(0 if ok else 1)" || { echo "KN4-1 FAIL"; exit 1; }
J=$D/sel_jobs.txt; : > $J; SS="650 651 652 653 654 655"
for k in 0 1; do echo "R_k$k scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$k --fleet PL:$P/L11_s13_fleet.pt" >> $J
  for g in all w:3 w:6 w:10 h:10 h:20 h:30 wh:3,10 wh:3,20 wh:3,30 wh:6,10 wh:6,20 wh:6,30 wh:10,10 wh:10,20 wh:10,30; do T=S_$(echo $g | tr -d ':' | tr ',' '_')_k$k
    echo "$T scripts/CITY_eval_n4.py --n4 0.5:$g:$M/n2_k$k.pt --light RL-H:$k --fleet PL:$P/L11_s13_fleet.pt" >> $J; done; done
export PY D SS; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/sel/$T.json ] || nice -n 5 $PY -u "$@" --seeds $SS --tag $T --out $D/sel >> $D/sel/run.log 2>&1 || echo "FAIL $T"' < $J
echo "select done $(date)"; $PY scripts/CITY_n4_select.py > $D/sel/select.txt || { echo "SELECT FAIL"; exit 1; }; tail -1 $D/sel/select.txt
CH=$D/sel/choice.json; GS=$($PY -c "import json;print(json.load(open('$CH'))['G'])"); WS=$($PY -c "import json;print(json.load(open('$CH'))['W'])"); HS=$($PY -c "import json;print(json.load(open('$CH'))['H'])"); PP=$($PY -c "import json;print(json.load(open('$CH'))['p'])")
J=$D/dev_jobs.txt; : > $J
for k in 0 1; do for fl in s13 s113; do F="--light RL-H:$k --fleet PL:$P/L11_${fl}_fleet.pt"
  echo "G_k${k}_${fl} scripts/CITY_eval_n4.py --n4 0.5:$GS:$M/n2_k$k.pt $F" >> $J; echo "W_k${k}_${fl} scripts/CITY_eval_n4.py --n4 0.5:$WS:$M/n2_k$k.pt $F" >> $J
  echo "H_k${k}_${fl} scripts/CITY_eval_n4.py --n4 0.5:$HS:$M/n2_k$k.pt $F" >> $J; echo "RND_k${k}_${fl} scripts/CITY_eval_n4.py --n4 0.5:rnd:$PP:$M/n2_k$k.pt $F" >> $J; done; done
export SS="600 601 602 603 604 605 606 607 608 609 610 611"; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/dev/$T.json ] || nice -n 5 $PY -u "$@" --seeds $SS --tag $T --out $D/dev >> $D/dev/run.log 2>&1 || echo "FAIL $T"' < $J
echo "panel done $(date)"; $PY scripts/CITY_n4_report.py; echo "N4 done $(date)"
