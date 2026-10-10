#!/usr/bin/env bash
# W16 stage 1 (PROTOCOL_CITY_WAVE16_20261008 + A1, A2): the IDM world (every car the Peachtree-calibrated IDM via CITY_w16_idm).
# Training under IDM: lights RL-H t24-t28 (120 ep), fleets R10 s1813-s2113 (400 ep, FT signals, exact FT SPaT).  Fresh traffic 1300-1319
# (non-existence check).  Rows: OFF / PL / R under FT; GATE / RL under the learned lights; x HBEFA4 / PHEMlight5 (W16_EM), modes logger.
# Report D16-1 (M1-IDM), W16-2 (light gate), M2 descriptive.   SMOKE=1: t24, s1813, 1-episode trainings, seed 860, into W16_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W16_DIR:-research/city_sim/w16_20261008}/fresh4; mkdir -p $D/lights $D/fleets $D/m1 $D/check
export XPLAY_TMP=$(cd $D/check && pwd) W16_LIGHTS=$(cd $D/lights && pwd); G=research/city_sim/demand/grid4
RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; RUN="$PY -u scripts/CITY_w16_idm.py"; P5=PHEMlight5/PC_EU4_G
echo "W16-S1 start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="24"; FS="1813"; LEP=1; FEP=1; CS="860"
else SM=""; LT="24 25 26 27 28"; FS="1813 1913 2013 2113"; LEP=120; FEP=400; CS="$(seq -s ' ' 1300 1319)"; fi
# 1. training in the IDM world
for k in $LT; do [ -f $D/lights/RL-H_t$k.pt ] || nice -n 5 $RUN scripts/CITY_q7b_contract.py --out $D/lights --train-light RL-H_t$k --t $k --episodes $LEP $SM > $D/lights/train_t$k.out 2>&1 & done
for s in $FS; do [ -f $D/fleets/L11_s${s}_fleet.pt ] || nice -n 5 $RUN scripts/CITY_fleet_train_v11_ppo.py --spat on --seed $s --episodes $FEP --name L11_s$s --out $D/fleets --resume $SM > $D/fleets/L11_s$s.out 2>&1 & done
wait; echo "training done $(date)"
for k in $LT; do [ -f $D/lights/RL-H_t$k.pt ] && grep -q "KW16-0: type v_passenger tau 0.742" $D/lights/train_t$k.out || { echo "KW16-1 FAIL light t$k"; tail -3 $D/lights/train_t$k.out; exit 1; }; done
for s in $FS; do [ -f $D/fleets/L11_s${s}_fleet.pt ] && grep -q "KW16-0: type v_passenger tau 0.742" $D/fleets/L11_s$s.out || { echo "KW16-1 FAIL fleet s$s"; tail -3 $D/fleets/L11_s$s.out; exit 1; }; done; echo "KW16-1 PASS (training)"
# 2. fresh traffic 1300-1319
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF1300_generated ]; then
  for s in $CS; do [ -f $G/rou_s$s.xml ] && { echo "KW16-2 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $CS; do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF1300_generated; echo "traffic 1300-1319 generated $(date)"; fi
# 3. rows
J=$D/m1_jobs.txt; : > $J
for x in "" P5; do E="-"; [ -z "$x" ] || E=$P5
  echo "OFF${x}_t0_h $E scripts/CITY_eval6_v11.py --light FT --fleet L-ACT:0 --guard always" >> $J
  for s in $FS; do P="PL:$D/fleets/L11_s${s}_fleet.pt"
    echo "PL${x}_t0_s$s $E scripts/CITY_eval6_v11.py --light FT --fleet $P" >> $J
    echo "R${x}_t0_s$s $E scripts/CITY_eval_f1.py --spat-arm none --light FT --fleet $P" >> $J; done
  for k in $LT; do echo "GATE${x}_t${k}_h $E scripts/CITY_eval6_v11.py --light RL-H:$k --fleet L-ACT:0 --guard always" >> $J
    for s in $FS; do echo "RL${x}_t${k}_s$s $E scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$k --fleet PL:$D/fleets/L11_s${s}_fleet.pt" >> $J; done; done; done
export PY SM OUT=$D/m1 SS="$CS"
xargs -P 6 -L 1 bash -c 'T=$0; E=$1; shift; [ -f $OUT/$T.json ] && exit 0; if [ "$E" != "-" ]; then export W16_EM=$E; fi
  nice -n 5 $PY -u scripts/CITY_w16_idm.py scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "rows failure: stop"; exit 1; }
grep -c "KW16-0: type v_passenger tau 0.742" $D/m1/run.log; grep -q "KW16-0 FAIL" $D/m1/run.log && { echo "KW16-0 FAIL in rows: stop"; exit 1; }
W16_SMOKE=${SMOKE:-0} $PY scripts/CITY_w16_report.py m1 $D || { echo "report FAIL"; exit 1; }
echo "W16-S1 done $(date)"
