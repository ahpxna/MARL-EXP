#!/usr/bin/env bash
# W18 screen (PROTOCOL_CITY_WAVE18_20261008): field-matched world (CITY_w18_world -> CITY_w17_world), FT.  Training (parallel, 400 ep):
# D1 off-peak R10 fleets s3613 / s3713 (W18_DEMAND=p4), D2b queue-aware no-creep PPO s3213 / s3313 (W18_FLEET=Q), D3 PHEMlight5-trained
# s3413 / s3513 (W17_EM).  D2a = zero-residual CarPPOLQ (rule).  Screen rows on TUNE 660-663 (off-peak: grid4_p4 660-663) x HBEFA4 /
# PHEMlight5 -> candidates per family.   SMOKE=1: 1-episode trainings, seed 660, one fleet per family, into W18_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W18_DIR:-research/city_sim/w18_20261008}; mkdir -p $D/fleets $D/screen $D/check; export XPLAY_TMP=$(cd $D/check && pwd)
RUN="$PY -u scripts/CITY_w18_world.py"; P5=PHEMlight5/PC_EU4_G; W17F=research/city_sim/w17_20261008/fresh5/fleets; echo "W18-SCREEN start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; EP=1; TS="660"; F1="3613"; F2="3213"; F3="3413"; FB="2213"; else SM=""; EP=400; TS="660 661 662 663"; F1="3613 3713"; F2="3213 3313"; F3="3413 3513"; FB="2213 2313 2413 2513"; fi
for s in $F1; do [ -f $D/fleets/D1_s${s}_fleet.pt ] || W18_DEMAND=p4 nice -n 5 $RUN scripts/CITY_fleet_train_v11_ppo.py --spat on --seed $s --episodes $EP --name D1_s$s --out $D/fleets --resume $SM > $D/fleets/D1_s$s.out 2>&1 & done
for s in $F2; do [ -f $D/fleets/D2b_s${s}_fleet.pt ] || W18_FLEET=Q nice -n 5 $RUN scripts/CITY_fleet_train_v11_ppo.py --spat on --seed $s --episodes $EP --name D2b_s$s --out $D/fleets --resume $SM > $D/fleets/D2b_s$s.out 2>&1 & done
for s in $F3; do [ -f $D/fleets/D3_s${s}_fleet.pt ] || W17_EM=$P5 nice -n 5 $RUN scripts/CITY_fleet_train_v11_ppo.py --spat on --seed $s --episodes $EP --name D3_s$s --out $D/fleets --resume $SM > $D/fleets/D3_s$s.out 2>&1 & done
wait; echo "training done $(date)"
for f in $(for s in $F1; do echo D1_s$s; done) $(for s in $F2; do echo D2b_s$s; done) $(for s in $F3; do echo D3_s$s; done); do
  [ -f $D/fleets/${f}_fleet.pt ] && grep -q "KW17-0: type v_passenger tau" $D/fleets/$f.out || { echo "KW18-0 FAIL $f: stop"; tail -3 $D/fleets/$f.out; exit 1; }; done; echo "KW18-0 PASS (training)"
[ -f $D/fleets/D2a_rule.pt ] || $PY -c "
import sys, torch; sys.path.insert(0,'.'); import scripts.CITY_fleet_v9 as V9
torch.save(dict(net=V9.NetR(3213), kind='w18_D2a_rule'), '$D/fleets/D2a_rule.pt')"
J=$D/screen_jobs.txt; : > $J
for x in "" P5; do E="-"; [ -z "$x" ] || E=$P5
  echo "OFF${x}_t0_h - $E --light FT --fleet L-ACT:0 --guard always" >> $J
  echo "OFF75${x}_t0_h RHO=0.75 $E --light FT --fleet L-ACT:0 --guard always" >> $J
  echo "OFF100${x}_t0_h RHO=1.0 $E --light FT --fleet L-ACT:0 --guard always" >> $J
  echo "OFFP4${x}_t0_h DEM=p4 $E --light FT --fleet L-ACT:0 --guard always" >> $J
  for s in $FB; do echo "BASE${x}_t0_s$s - $E --light FT --fleet PL:$W17F/L11_s${s}_fleet.pt" >> $J
    echo "D4a${x}_t0_s$s RHO=0.75 $E --light FT --fleet PL:$W17F/L11_s${s}_fleet.pt" >> $J; echo "D4b${x}_t0_s$s RHO=1.0 $E --light FT --fleet PL:$W17F/L11_s${s}_fleet.pt" >> $J; done
  for s in $F1; do echo "D1${x}_t0_s$s DEM=p4 $E --light FT --fleet PL:$D/fleets/D1_s${s}_fleet.pt" >> $J; done
  echo "D2a${x}_t0_r - $E --light FT --fleet PLQ:$D/fleets/D2a_rule.pt" >> $J
  for s in $F2; do echo "D2b${x}_t0_s$s - $E --light FT --fleet PLQ:$D/fleets/D2b_s${s}_fleet.pt" >> $J; done
  for s in $F3; do echo "D3${x}_t0_s$s - $E --light FT --fleet PL:$D/fleets/D3_s${s}_fleet.pt" >> $J; done
  for g in 1.0 1.5 2.0; do t=$(echo $g | tr -d '.'); echo "D5g${t}${x}_t0_g - $E --light FT --fleet GENTLE:$g" >> $J; done; done
export PY SM OUT=$D/screen SS="$TS"
xargs -P 6 -L 1 bash -c 'T=$0; V=$1; E=$2; shift 2; [ -f $OUT/$T.json ] && exit 0
  case $V in RHO=*) export W18_RHO=${V#RHO=};; DEM=*) export W18_DEMAND=${V#DEM=};; esac; if [ "$E" != "-" ]; then export W17_EM=$E; fi
  nice -n 5 $PY -u scripts/CITY_w18_world.py scripts/CITY_w13_modes.py scripts/CITY_eval6_v11.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "screen failure: stop"; exit 1; }
grep -q "KW17-0 FAIL" $D/screen/run.log && { echo "KW18-0 FAIL in rows: stop"; exit 1; }
W18_SMOKE=${SMOKE:-0} $PY scripts/CITY_w18_report.py screen $D || { echo "screen report FAIL"; exit 1; }
echo "W18-SCREEN done $(date)"
