#!/usr/bin/env bash
# W15-1 (PROTOCOL_CITY_WAVE15_20261007): FRESH3 = new lights RL-H t19-t23 (120 ep) + fleets R10 s1413-s1713 (400 ep) + F1-B (200 ep);
# forecaster calibration by the FRESH2 recipe (traces -> open-loop -> closed-loop c2 [KF-3] -> N2 logs -> fit [KF-2]); TRB tuning grid for
# comparison (C x q {0.1, 0.5} x HBEFA4 / PHEMlight5, TUNE 660-663) -> R13-RB; fresh traffic 1040-1059; R, TG (default 1, 0.25, 0.1), TRB,
# F1B x HBEFA4 / PHEMlight5; report D15-1 / D15-1b.   SMOKE=1: one light / fleet, 1-episode trainings, 600 s, seeds 0-7 / 660 / 860.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W15_DIR:-research/city_sim/w15_20261007}/fresh3; mkdir -p $D/lights $D/fleets $D/f1b $D/traces $D/m2b $D/prep $D/cdata $D/cmodel $D/check $D/tune $D/conf
export XPLAY_TMP=$(cd $D/check && pwd) W7_FPR_DIR=$(cd $D && pwd) W15_LIGHTS=$(cd $D/lights && pwd); G=research/city_sim/demand/grid4
RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt
RUN="$PY -u scripts/CITY_w15_run.py"; P5=em:PHEMlight5/PC_EU4_G; echo "W15-FRESH3 start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="19"; FS="1413"; LEP=1; FEP=1; FEP2=1; TS="0 1 2 3 4 5 6 7"; TUNES="660"; CS="860"; NF=1; export W7_PREP_N=1 W7_PREP_END=300
else SM=""; LT="19 20 21 22 23"; FS="1413 1513 1613 1713"; LEP=120; FEP=400; FEP2=200; TS="0 1 2 3 4 5 6 7"; TUNES="660 661 662 663"; CS="$(seq -s ' ' 1040 1059)"; NF=8; fi
# 1. training
for k in $LT; do [ -f $D/lights/RL-H_t$k.pt ] || nice -n 5 $PY -u scripts/CITY_q7b_contract.py --out $D/lights --train-light RL-H_t$k --t $k --episodes $LEP $SM > $D/lights/train_t$k.out 2>&1 & done
for s in $FS; do [ -f $D/fleets/L11_s${s}_fleet.pt ] || nice -n 5 $PY -u scripts/CITY_fleet_train_v11_ppo.py --spat on --seed $s --episodes $FEP --name L11_s$s --out $D/fleets --resume $SM > $D/fleets/L11_s$s.out 2>&1 & done
wait; echo "training done $(date)"
for k in $LT; do [ -f $D/lights/RL-H_t$k.pt ] || { echo "KF-1 FAIL light t$k"; tail -3 $D/lights/train_t$k.out; exit 1; }; done
for s in $FS; do [ -f $D/fleets/L11_s${s}_fleet.pt ] || { echo "KF-1 FAIL fleet s$s"; tail -3 $D/fleets/L11_s$s.out; exit 1; }; done; echo "KF-1 PASS"
# 2. traces and open-loop tables
for k in $LT; do [ -f $D/traces/fit_RLH$k.json ] || nice -n 5 $RUN scripts/CITY_eval4_sigma.py --sigma 0.3 --light RL-H:$k --fleet L-ACT:0 --guard always --seeds $TS $SM --record $D/traces/rlh${k}_s{seed}.npz --tag fit_RLH$k --out $D/traces >> $D/traces/run.log 2>&1 & done; wait
for k in $LT; do F=""; for s in $TS; do F="$F $D/traces/rlh${k}_s$s.npz"; done; $RUN scripts/CITY_spat_forecast.py fit $k $D/m2b/forecast_rlh$k.json $F > $D/m2b/fit_t$k.log 2>&1 || { echo "open-loop fit FAIL t$k"; tail -3 $D/m2b/fit_t$k.log; exit 1; }; done
# 3. closed-loop c2 prep + KF-3
for k in $LT; do [ -f $D/prep/prov_rlh${k}_cl.json ] || nice -n 5 $PY -u scripts/CITY_w15_prep.py $k $D/prep > $D/prep/prep_k$k.out 2>&1 & done; wait
for k in $LT; do $PY -c "
import json; T = json.load(open('$D/prep/prov_rlh${k}_cl.json')); assert len(T['per']) == 16 and T['n_files'] == $NF, (len(T['per']), T['n_files']); print('KF-3 t$k ok')" || { echo "KF-3 FAIL t$k"; exit 1; }; done
# 4. F1-B (background): fleet i from scratch under light t(19+i)
set -- $LT; LA=($@); i=0; for s in $FS; do k=${LA[$i]}; [ -f $D/f1b/F1B_s${s}_t${k}_fleet.pt ] || nice -n 5 $RUN scripts/CITY_fleet_train_f1b.py --seed $s --light-k $k --init scratch --table $D/prep/prov_rlh${k}_cl.json --q 0.1 --episodes $FEP2 $SM --name F1B_s${s}_t$k --out $D/f1b > $D/f1b/F1B_s${s}_t$k.out 2>&1 & i=$((i+1)); done
# 5. N2 logs, fits, KF-2
J=$D/collect_jobs.txt; : > $J; for k in $LT; do for s in $TS; do echo "$k $s" >> $J; done; done
export PY D RUN SM DEV; xargs -P 4 -L 1 bash -c '[ -f $D/cdata/c2_t$0/feat_s$1.npz ] || nice -n 5 $RUN scripts/CITY_n2_collect.py --featlog $D/cdata/c2_t$0 --spat-arm fc2:0.1:$D/prep/prov_rlh$0_cl.json --light RL-H:$0 --fleet PL:$DEV --seeds $1 $SM --tag C_t$0_s$1 --out $D/cdata/c2_t$0 >> $D/cdata/run.log 2>&1 || { echo "FAIL collect $0 $1"; exit 255; }' < $J || { echo "collection failure: stop"; exit 1; }
for k in $LT; do [ -f $D/cmodel/n2_k$k.pt ] || $PY -u scripts/CITY_n2_fit.py $k $D/cdata/c2_t$k $D/cmodel > $D/cmodel/fit_t$k.log 2>&1 || { echo "FIT FAIL t$k"; exit 1; }; done
K1=$(echo $LT | cut -d' ' -f1); F1=$(echo $FS | cut -d' ' -f1); K=$D/check/kf2_t$K1; mkdir -p $K
$RUN scripts/CITY_eval_n2.py --n2 0.5:$D/cmodel/n2_k$K1.pt --featlog $K --light RL-H:$K1 --fleet PL:$D/fleets/L11_s${F1}_fleet.pt --seeds 0 --smoke --tag KF2_n2 --out $K > $K/run.log 2>&1 || { echo "KF-2 run FAIL"; exit 1; }
$PY scripts/CITY_n2_parity.py $K 0 $D/cmodel/n2_k$K1.pt | tee $D/check/kf2.txt || { echo "KF-2 FAIL: stop"; exit 1; }
# 6. TRB tuning grid (comparison only; TG is fixed in advance)
GRID="1:0 1.5:0 2:0 1:0.25 1.5:0.25 2:0.25 1:0.5 1.5:0.5 2:0.5 3:0.5"; N4() { echo "--n4 $2:hyb:$D/prep/prov_rlh$1_cl.json:$D/cmodel/n2_k$1.pt"; }
J=$D/tune_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$DEV"
  for em in none $P5; do x=""; [ "$em" = none ] || x="_P5"; echo "R_t${k}$x $em scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
    for g in $GRID; do a=${g%%:*}; b=${g##*:}; T="T_t${k}_a${a//./p}_b${b//./p}"
      echo "${T}$x $em scripts/CITY_eval_n4.py $(N4 $k 0.5) $F --light-obs q:$a:$b" >> $J; echo "${T}_q01$x $em scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:$a:$b" >> $J; done; done; done
run_jobs() { export PY SM; export OUT=$2 SS="$3"
  xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $OUT/$T.json ] || nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_w15_run.py scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
run_jobs $J $D/tune "$TUNES" || { echo "tuning failure: stop"; exit 1; }
$PY -c "import json; json.dump(dict(name='FRESH3', dir='$D', lights=[int(x) for x in '$LT'.split()], fleets=['s'+x for x in '$FS'.split()], tune_old='$D/tune', choice_old='', tune_seeds=[int(x) for x in '$TUNES'.split()], conf_seeds=[int(x) for x in '$CS'.split()], f1b=True), open('$D/panel.json','w'), indent=1)"
W14_SMOKE=0 $PY scripts/CITY_w14_gen.py select $D/panel.json || { echo "selection FAIL: stop"; exit 1; }
# 7. fresh traffic 1040-1059
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF1040_generated ]; then
  for s in $CS; do [ -f $G/rou_s$s.xml ] && { echo "KW15-1 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $CS; do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF1040_generated; echo "traffic 1040-1059 generated $(date)"; fi
# 8. confirmation (after F1-B)
wait; i=0; for s in $FS; do k=${LA[$i]}; [ -f $D/f1b/F1B_s${s}_t${k}_fleet.pt ] || { echo "missing F1B_s${s}_t$k: stop"; tail -3 $D/f1b/F1B_s${s}_t$k.out; exit 1; }; i=$((i+1)); done
CH() { $PY -c "import json;c=json.load(open('$1'))['$2']['choice'].split(',');print(c[0]+':'+c[1]+' '+(c[2] if len(c)>2 else '0.5'))"; }
J=$D/conf_jobs.txt; : > $J
for k in $LT; do read RAB RQ <<< "$(CH $D/tune/choice_RB.json $k)"
  for s in $FS; do F="--light RL-H:$k --fleet PL:$D/fleets/L11_s${s}_fleet.pt"; i=0; for x in $FS; do [ "$x" = "$s" ] && break; i=$((i+1)); done; kf=${LA[$i]}
    for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
      echo "R${x}_t${k}_s$s $em scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
      echo "TG${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:1:0.25" >> $J
      echo "TRB${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $(N4 $k $RQ) $F --light-obs q:$RAB" >> $J
      echo "F1B${x}_t${k}_s$s $em scripts/CITY_eval_f1b.py --spat-arm fc2:0.1:$D/prep/prov_rlh${k}_cl.json --light RL-H:$k --fleet PL:$D/f1b/F1B_s${s}_t${kf}_fleet.pt" >> $J; done; done; done
run_jobs $J $D/conf "$CS" || { echo "confirmation failure: stop"; exit 1; }
if [ "${SMOKE:-0}" = 1 ]; then W15_SMOKE=1 W15_SEED=860 $PY scripts/CITY_w15_zs_report.py $D; else $PY scripts/CITY_w15_zs_report.py $D; fi || { echo "report FAIL"; exit 1; }
echo "W15-FRESH3 done $(date)"
