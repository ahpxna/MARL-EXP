#!/usr/bin/env bash
# W13-4 (PROTOCOL_CITY_WAVE13_20261006, Amendment A1): iterated closed-loop refit on FRESH2 t14-t18.  Configuration per light: R13-RB if 084's
# D13-2 was SHOWN, else R13-F.  Round r (1, 2): collect TRAIN 0-7 logs with the development fleet while TSI (round r-1 network) is published ->
# CITY_n2_fit -> KF-2 parity on t14; TUNE 660-663 under HBEFA4 / PHEMlight5 for rounds 1, 2 (round 0 rows too); round selection; fresh traffic
# 920-939 (non-existence check): R, TC, TREF, F1B x t14-t18 x s1013-s1313 x 20 (HBEFA4 / PHEMlight5); report D13-1', D13-2'.
# SMOKE=1: t14, TRAIN 0-1 (300 s), TUNE 660, conf t14 x s1013 x 860, 600 s, into W13_DIR (needs a smoke 083/084 there).
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W13_DIR:-research/city_sim/w13_20261006}; F2=research/city_sim/w8_20261005/fresh2; DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P5=em:PHEMlight5/PC_EU4_G; R=$D/refit
mkdir -p $R/tune $R/conf $R/check; export XPLAY_TMP=$(cd $R/check && pwd); echo "W13-REFIT start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="14"; TRS="0 1 2 3 4 5 6 7"; TS="660"; FS="1013"; CS="860"; else SM=""; LT="14 15 16 17 18"; TRS="0 1 2 3 4 5 6 7"; TS="660 661 662 663"; FS="1013 1113 1213 1313"; CS="$(seq -s ' ' 920 939)"; fi
[ -f $D/conf/report_conf.txt ] || { echo "084 report missing: stop"; exit 1; }
if grep -q "D13-2 VERDICT: saving under both HBEFA4 and PHEMlight5 SHOWN" $D/conf/report_conf.txt; then CF=choice_RB.json; else CF=choice_F.json; fi; echo "configuration: $CF"
$PY -c "
import json; c=json.load(open('$D/tune/$CF')); out={}
for t,v in c.items():
    a,b,*q=v['choice'].split(','); out[t]=[a,b,q[0] if q else '0.5']
json.dump(dict(source='$CF', lights=out), open('$R/config.json','w'), indent=1)"
CFG() { $PY -c "import json;v=json.load(open('$R/config.json'))['lights']['$1'];print(v[0]+':'+v[1], v[2])"; }
MODEL() { [ "$2" = 0 ] && echo "$F2/cmodel/n2_k$1.pt" || echo "$R/model_r$2/n2_k$1.pt"; }
for r in 1 2; do p=$((r - 1)); mkdir -p $R/data_r$r $R/model_r$r; J=$R/collect_r$r.txt; : > $J
  for k in $LT; do read AB Q <<< "$(CFG $k)"; for s in $TRS; do echo "$k $s $AB $Q $(MODEL $k $p)" >> $J; done; done
  export PY R SM DEV F2 r; xargs -P 6 -L 1 bash -c '[ -f $R/data_r$r/t$0/feat_s$1.npz ] || nice -n 5 $PY -u scripts/CITY_w9_run.py none scripts/CITY_eval_n4f.py --n4 $3:hyb:$F2/prep/prov_rlh$0_cl.json:$4 --featlog $R/data_r$r/t$0 --light RL-H:$0 --fleet PL:$DEV --light-obs q:$2 --seeds $1 $SM --tag C_t$0_s$1 --out $R/data_r$r/t$0 >> $R/data_r$r/run.log 2>&1 || { echo "FAIL collect r$r $0 $1"; exit 255; }' < $J || { echo "collection failure r$r: stop"; exit 1; }
  for k in $LT; do [ -f $R/model_r$r/n2_k$k.pt ] || $PY -u scripts/CITY_n2_fit.py $k $R/data_r$r/t$k $R/model_r$r > $R/model_r$r/fit_t$k.log 2>&1 || { echo "FIT FAIL r$r t$k"; tail -3 $R/model_r$r/fit_t$k.log; exit 1; }; done
  K1=$(echo $LT | cut -d' ' -f1); K=$R/check/kf2_r${r}_t$K1; mkdir -p $K
  $PY -u scripts/CITY_w9_run.py none scripts/CITY_eval_n2.py --n2 0.5:$R/model_r$r/n2_k$K1.pt --featlog $K --light RL-H:$K1 --fleet PL:$DEV --seeds 0 --smoke --tag KF2 --out $K > $K/run.log 2>&1 || { echo "KF-2 run FAIL r$r"; exit 1; }
  $PY scripts/CITY_n2_parity.py $K 0 $R/model_r$r/n2_k$K1.pt | tee $R/check/kf2_r$r.txt || { echo "KF-2 FAIL r$r: stop"; exit 1; }
  echo "round $r fitted $(date)"; done
# TUNE rows: R and rounds 0-2 under both models
J=$R/tune_jobs.txt; : > $J
for k in $LT; do read AB Q <<< "$(CFG $k)"; F="--light RL-H:$k --fleet PL:$DEV"
  for em in none $P5; do x=""; [ "$em" = none ] || x="P5"; echo "R_t${k}${x} $em scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
    for r in 0 1 2; do echo "TR${r}_t${k}${x} $em scripts/CITY_eval_n4.py --n4 $Q:hyb:$F2/prep/prov_rlh${k}_cl.json:$(MODEL $k $r) $F --light-obs q:$AB" >> $J; done; done; done
export PY R SM; export SS="$TS"
xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $R/tune/$T.json ] || nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $R/tune >> $R/tune/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "tuning failure: stop"; exit 1; }
if [ "${SMOKE:-0}" = 1 ]; then W13_SMOKE=1 $PY scripts/CITY_w13_refit.py select $D; else $PY scripts/CITY_w13_refit.py select $D; fi || { echo "selection FAIL"; exit 1; }
# fresh traffic 920-939
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF920_generated ]; then
  for s in $(seq 920 939); do [ -f $G/rou_s$s.xml ] && { echo "KW13-4 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 920 939); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF920_generated; echo "traffic 920-939 generated $(date)"; fi
J=$R/conf_jobs.txt; : > $J
for k in $LT; do read AB Q <<< "$(CFG $k)"; RR=$($PY -c "import json;print(json.load(open('$R/choice.json'))['$k']['round'])")
  for s in $FS; do F="--light RL-H:$k --fleet PL:$F2/fleets/L11_s${s}_fleet.pt"; F1B=$(grep "^F1B_t${k}_s$s " $F2/conf_jobs.txt | cut -d' ' -f2-)
    for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
      echo "R${x}_t${k}_s$s $em scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
      echo "TC${x}_t${k}_s$s $em scripts/CITY_eval_n4.py --n4 $Q:hyb:$F2/prep/prov_rlh${k}_cl.json:$(MODEL $k 0) $F --light-obs q:$AB" >> $J
      echo "TREF${x}_t${k}_s$s $em scripts/CITY_eval_n4.py --n4 $Q:hyb:$F2/prep/prov_rlh${k}_cl.json:$(MODEL $k $RR) $F --light-obs q:$AB" >> $J
      echo "F1B${x}_t${k}_s$s $em $F1B" >> $J; done; done; done
export SS="$CS"
xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $R/conf/$T.json ] || nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $R/conf >> $R/conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation failure: stop"; exit 1; }
if [ "${SMOKE:-0}" = 1 ]; then W13_SMOKE=1 $PY scripts/CITY_w13_refit.py report $D; else $PY scripts/CITY_w13_refit.py report $D; fi || { echo "report FAIL"; exit 1; }
echo "W13-REFIT done $(date)"
