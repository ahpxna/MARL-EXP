#!/usr/bin/env bash
# W17 stage 2 (PROTOCOL_CITY_WAVE17_20261008), only after stage 1 passed D17-1 and W17-2: in the field-matched world, F1-B (fleets from scratch,
# 200 ep, fleet i under light t(29+i)), forecaster calibration as W15-1 (traces -> open-loop -> c2 prep [KF-3] -> N2 logs -> fit [KF-2]),
# tuning (R, the W13 grid x q, the 27 state quantiles; HBEFA4 / PHEMlight5; TUNE 660-663) -> R15-U; fresh 1340-1359; R, TG, TU, F1B -> D16-2/3.
# SMOKE=1: t29, s2213, 1-episode F1-B, TS 0-7 at 300 s, TUNE 660, conf 860, into W17_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W17_DIR:-research/city_sim/w17_20261008}/fresh5; mkdir -p $D/f1b $D/traces $D/m2b $D/prep $D/cdata $D/cmodel $D/check $D/tune $D/conf
export XPLAY_TMP=$(cd $D/check && pwd) W7_FPR_DIR=$(cd $D && pwd) W17_LIGHTS=$(cd $D/lights && pwd); G=research/city_sim/demand/grid4
RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt
RUN="$PY -u scripts/CITY_w17_world.py"; P5=PHEMlight5/PC_EU4_G; echo "W17-S2 start $(date)"
[ "${SMOKE:-0}" = 1 ] || { $PY -c "import json,sys; d=json.load(open('$D/m1/stage1.json')); sys.exit(0 if d['D17_1'] and d['W17_2'] else 1)" || { echo "stage 1 did not pass: stop"; exit 1; }; }
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="29"; FS="2213"; FEP2=1; TS="0 1 2 3 4 5 6 7"; TUNES="660"; CS="860"; NF=1; export W7_PREP_N=1 W7_PREP_END=300; QSL="-2:1:1 2:0:0"
else SM=""; LT="29 30 31 32 33"; FS="2213 2313 2413 2513"; FEP2=200; TS="0 1 2 3 4 5 6 7"; TUNES="660 661 662 663"; CS="$(seq -s ' ' 1340 1359)"; NF=8
  QSL=""; for a in -2 0 2; do for b in 0 1 3; do for c in 0 1 3; do QSL="$QSL $a:$b:$c"; done; done; done; fi
# 1. traces + open-loop tables
for k in $LT; do [ -f $D/traces/fit_RLH$k.json ] || nice -n 5 $RUN scripts/CITY_eval4_sigma.py --sigma 0.3 --light RL-H:$k --fleet L-ACT:0 --guard always --seeds $TS $SM --record $D/traces/rlh${k}_s{seed}.npz --tag fit_RLH$k --out $D/traces >> $D/traces/run.log 2>&1 & done; wait
for k in $LT; do F=""; for s in $TS; do F="$F $D/traces/rlh${k}_s$s.npz"; done; $PY scripts/CITY_spat_forecast.py fit $k $D/m2b/forecast_rlh$k.json $F > $D/m2b/fit_t$k.log 2>&1 || { echo "open-loop fit FAIL t$k: stop"; tail -3 $D/m2b/fit_t$k.log; exit 1; }; done
# 2. closed-loop c2 prep + KF-3
for k in $LT; do [ -f $D/prep/prov_rlh${k}_cl.json ] || nice -n 5 $RUN scripts/CITY_w17_prep.py $k $D/prep > $D/prep/prep_k$k.out 2>&1 & done; wait
for k in $LT; do $PY -c "
import json; T = json.load(open('$D/prep/prov_rlh${k}_cl.json')); assert len(T['per']) == 16 and T['n_files'] == $NF, (len(T['per']), T['n_files']); print('KF-3 t$k ok')" || { echo "KF-3 FAIL t$k: stop"; exit 1; }; done
# 3. F1-B in the background
set -- $LT; LA=($@); i=0; for s in $FS; do k=${LA[$i]}; [ -f $D/f1b/F1B_s${s}_t${k}_fleet.pt ] || nice -n 5 $RUN scripts/CITY_fleet_train_f1b.py --seed $s --light-k $k --init scratch --table $D/prep/prov_rlh${k}_cl.json --q 0.1 --episodes $FEP2 $SM --name F1B_s${s}_t$k --out $D/f1b > $D/f1b/F1B_s${s}_t$k.out 2>&1 & i=$((i+1)); done
# 4. N2 logs, fits, KF-2
J=$D/collect_jobs.txt; : > $J; for k in $LT; do for s in $TS; do echo "$k $s" >> $J; done; done
export PY D RUN SM DEV; xargs -P 4 -L 1 bash -c '[ -f $D/cdata/c2_t$0/feat_s$1.npz ] || nice -n 5 $RUN scripts/CITY_n2_collect.py --featlog $D/cdata/c2_t$0 --spat-arm fc2:0.1:$D/prep/prov_rlh$0_cl.json --light RL-H:$0 --fleet PL:$DEV --seeds $1 $SM --tag C_t$0_s$1 --out $D/cdata/c2_t$0 >> $D/cdata/run.log 2>&1 || { echo "FAIL collect $0 $1"; exit 255; }' < $J || { echo "collect failure: stop"; exit 1; }
for k in $LT; do [ -f $D/cmodel/n2_k$k.pt ] || $PY -u scripts/CITY_n2_fit.py $k $D/cdata/c2_t$k $D/cmodel > $D/cmodel/fit_t$k.log 2>&1 || { echo "FIT FAIL t$k: stop"; exit 1; }; done
K1=$(echo $LT | cut -d' ' -f1); F1=$(echo $FS | cut -d' ' -f1); K=$D/check/kf2_t$K1; mkdir -p $K
$RUN scripts/CITY_eval_n2.py --n2 0.5:$D/cmodel/n2_k$K1.pt --featlog $K --light RL-H:$K1 --fleet PL:$D/fleets/L11_s${F1}_fleet.pt --seeds 0 --smoke --tag KF2_n2 --out $K > $K/run.log 2>&1 || { echo "KF-2 run FAIL: stop"; exit 1; }
$PY scripts/CITY_n2_parity.py $K 0 $D/cmodel/n2_k$K1.pt | tee $D/check/kf2.txt || { echo "KF-2 FAIL: stop"; exit 1; }
# 5. tuning: R, W13 grid x q, 27 state quantiles (dev fleet), HBEFA4 / PHEMlight5
GRID="1:0 1.5:0 2:0 1:0.25 1.5:0.25 2:0.25 1:0.5 1.5:0.5 2:0.5 3:0.5"; N4() { echo "--n4 $2:hyb:$D/prep/prov_rlh$1_cl.json:$D/cmodel/n2_k$1.pt"; }
enc() { case $1 in -*) echo "m${1#-}";; *) echo "$1";; esac; }
run_jobs() { export PY SM; export OUT=$2 SS="$3"
  xargs -P 6 -L 1 bash -c 'T=$0; E=$1; QS=$2; shift 2; [ -f $OUT/$T.json ] && exit 0; if [ "$E" != "-" ]; then export W17_EM=$E; fi
    if [ "$QS" = "-" ]; then W=""; else W="scripts/CITY_w15_qstate.py"; export W15_QS=$QS; fi
    nice -n 5 $PY -u scripts/CITY_w17_world.py $W scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
J=$D/tune_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$DEV"
  for X in "" _P5; do E="-"; [ -z "$X" ] || E=$P5; echo "R_t${k}$X $E - scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
    for g in $GRID; do a=${g%%:*}; b=${g##*:}; T="T_t${k}_a${a//./p}_b${b//./p}"
      echo "${T}$X $E - scripts/CITY_eval_n4.py $(N4 $k 0.5) $F --light-obs q:$a:$b" >> $J; echo "${T}_q01$X $E - scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:$a:$b" >> $J; done
    for qs in $QSL; do IFS=: read a b c <<< "$qs"; echo "S_t${k}_a$(enc $a)_b$(enc $b)_c$(enc $c)$X $E $qs scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:1:0.25" >> $J; done; done; done
run_jobs $J $D/tune "$TUNES" || { echo "tuning failure: stop"; exit 1; }
W17_SMOKE=${SMOKE:-0} $PY scripts/CITY_w17_report.py select $D || { echo "selection FAIL: stop"; exit 1; }
# 6. fresh traffic 1340-1359
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF1340_generated ]; then
  for s in $CS; do [ -f $G/rou_s$s.xml ] && { echo "KW17-3 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $CS; do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF1340_generated; echo "traffic 1340-1359 generated $(date)"; fi
# 7. confirmation (after F1-B)
wait; i=0; for s in $FS; do k=${LA[$i]}; [ -f $D/f1b/F1B_s${s}_t${k}_fleet.pt ] || { echo "missing F1B_s${s}_t$k: stop"; tail -3 $D/f1b/F1B_s${s}_t$k.out; exit 1; }; i=$((i+1)); done
J=$D/conf_jobs.txt; : > $J
for k in $LT; do U=$($PY -c "
import json; c=json.load(open('$D/tune/choice_U.json'))['$k']['choice']; kind,_,v=c.partition(':')
print(('- '+v.split(',')[0]+':'+v.split(',')[1]+' '+v.split(',')[2]) if kind=='grid' else (v+' 1:0.25 0.1'))"); read UQS UAB UQ <<< "$U"
  for s in $FS; do F="--light RL-H:$k --fleet PL:$D/fleets/L11_s${s}_fleet.pt"; i=0; for x in $FS; do [ "$x" = "$s" ] && break; i=$((i+1)); done; kf=${LA[$i]}
    for X in "" P5; do E="-"; [ -z "$X" ] || E=$P5
      echo "R${X}_t${k}_s$s $E - scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
      echo "TG${X}_t${k}_s$s $E - scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:1:0.25" >> $J
      echo "TU${X}_t${k}_s$s $E $UQS scripts/CITY_eval_n4.py $(N4 $k $UQ) $F --light-obs q:$UAB" >> $J
      echo "F1B${X}_t${k}_s$s $E - scripts/CITY_eval_f1b.py --spat-arm fc2:0.1:$D/prep/prov_rlh${k}_cl.json --light RL-H:$k --fleet PL:$D/f1b/F1B_s${s}_t${kf}_fleet.pt" >> $J; done; done; done
run_jobs $J $D/conf "$CS" || { echo "confirmation failure: stop"; exit 1; }
grep -q "KW17-0 FAIL" $D/tune/run.log $D/conf/run.log && { echo "KW17-0 FAIL: stop"; exit 1; }
W17_SMOKE=${SMOKE:-0} $PY scripts/CITY_w17_report.py report $D || { echo "report FAIL"; exit 1; }
echo "W17-S2 done $(date)"
