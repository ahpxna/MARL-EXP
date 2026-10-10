#!/usr/bin/env bash
# W12-4 DCA-task (PROTOCOL_CITY_WAVE12_20261006, A3): KD-1 identity -> tuning (info / raw x t4-t8, 352 full rollouts, checkpoints 88/176/352)
# -> DEV selection (600-611, fleet L11_s13) -> fresh grid4 880-899 -> confirmation R / TSI2 / DCAS / DCAR x t4-t8 x s213-s513 x 20 -> report.
# SMOKE=1: budget 9 (600 s), t4, DEV seed 600, confirmation seed 860 (existing W11 traffic), 600 s, into W12_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W12_DIR:-research/city_sim/w12_20261006/dcas}; mkdir -p $D/check $D/dev $D/conf; export XPLAY_TMP=$(cd $D/check && pwd)
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py
P=research/city_sim/spat_pilot_20261004/fleets_v11; TB=research/city_sim/f1b_20261004/prep; MOD=research/city_sim/tsi_20261005/cmodel/c2
CH=research/city_sim/tsi2_20261005/tune/choice.json; RUN="$PY -u scripts/CITY_f1a1_run.py"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; END=600; export DCAS_SMOKE=1; LT="4"; BS="3 6 9"; DS="600"; FLS="s213"; CS="860"
else SM=""; END=5400; LT="4 5 6 7 8"; BS="88 176 352"; DS="$(seq -s ' ' 600 611)"; FLS="s213 s313 s413 s513"; CS="$(seq -s ' ' 880 899)"; fi
N4() { echo "scripts/CITY_eval_n4.py --n4 0.5:hyb:$TB/prov_rlh$1_cl.json:$MOD/n2_k$1.pt"; }
echo "W12-DCAS start $(date)"
# KD-1: with zero (identity) parameters each arm reproduces the plain hybrid-service run bit for bit (t4, s213, seed 660, 600 s)
$PY -c "
import sys, torch; sys.path.insert(0, '.')
import scripts.CITY_w12_dcas as DS, scripts.CITY_q7_cross_version as Q7
for m in ('info', 'raw'):
    torch.save({i: DS.new_layer(m).get_params_vector().clone() for i in sorted(Q7.NetInfo(Q7.NET_S).tls)}, '$D/check/zero_' + m + '.pt')" || exit 1
[ -f $D/check/KD_plain.json ] || $RUN $(N4 4) --light RL-H:4 --fleet PL:$P/L11_s213_fleet.pt --seeds 660 --smoke --tag KD_plain --out $D/check >> $D/check/kd.log 2>&1 || { echo "KD plain FAIL"; exit 1; }
for m in info raw; do [ -f $D/check/KD_$m.json ] || DCAS_MODE=$m DCAS_END=600 DCAS_PARAMS=$D/check/zero_$m.pt $RUN scripts/CITY_w12_dcas.py $(N4 4) --light RL-H:4 --fleet PL:$P/L11_s213_fleet.pt --seeds 660 --smoke --tag KD_$m --out $D/check >> $D/check/kd.log 2>&1 || { echo "KD $m FAIL"; exit 1; }; done
$PY -c "
import json; a=json.load(open('$D/check/KD_plain.json'))['rows'][0]
for m in ('info','raw'):
    b=json.load(open('$D/check/KD_'+m+'.json'))['rows'][0]; ok=abs(a['timeloss']-b['timeloss'])<1e-9 and abs(a['fuel']-b['fuel'])<1e-6
    print('KD-1', m, 'identity == plain hybrid service:', ok, round(a['timeloss'],4), round(b['timeloss'],4)); assert ok" || { echo "KD-1 FAIL: stop"; exit 1; }
# tuning
for m in info raw; do mkdir -p $D/tune_$m; for t in $LT; do [ -f $D/tune_$m/dcas_${m}_t$t.json ] || nice -n 5 $PY -u scripts/CITY_w12_dcas_tune.py $t $m $D/tune_$m > $D/tune_$m/tune_t$t.log 2>&1 & done; done; wait
for m in info raw; do for t in $LT; do for b in $BS; do [ -f $D/tune_$m/dcas_${m}_t${t}_b$b.pt ] || { echo "tuning failed $m t$t b$b"; tail -3 $D/tune_$m/tune_t$t.log; exit 1; }; done; done; done; echo "tuning done $(date)"
# DEV selection
J=$D/dev_jobs.txt; : > $J
for t in $LT; do echo "R_DEV_t$t none none scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$t --fleet PL:$P/L11_s13_fleet.pt" >> $J
  for m in info raw; do for b in $BS; do echo "DEV_${m}_t${t}_b$b $m $D/tune_$m/dcas_${m}_t${t}_b$b.pt $(N4 $t) --light RL-H:$t --fleet PL:$P/L11_s13_fleet.pt" >> $J; done; done; done
export PY D RUN SM END
xargs -P 6 -L 1 bash -c 'T=$0; M=$1; PP=$2; shift 2; [ -f $D/dev/$T.json ] && exit 0; if [ "$M" = none ]; then DCAS_END=$END nice -n 5 $RUN scripts/CITY_w12_dcas.py "$@" --seeds '"$DS"' $SM --tag $T --out $D/dev >> $D/dev/run.log 2>&1; else DCAS_MODE=$M DCAS_END=$END DCAS_PARAMS=$PP nice -n 5 $RUN scripts/CITY_w12_dcas.py "$@" --seeds '"$DS"' $SM --tag $T --out $D/dev >> $D/dev/run.log 2>&1; fi || { echo "FAIL $T"; exit 255; }' < $J || { echo "DEV runs failed: stop"; exit 1; }
if [ "${SMOKE:-0}" = 1 ]; then W12_SMOKE=1 $PY scripts/CITY_w12_dcas_select.py $D; else $PY scripts/CITY_w12_dcas_select.py $D; fi || { echo "selection FAIL"; exit 1; }
# fresh confirmation traffic 880-899
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF880_generated ]; then for s in $(seq 880 899); do [ -f $G/rou_s$s.xml ] && { echo "KW12-4 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 880 899); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; date > $G/CONF880_generated; fi
# confirmation
J=$D/conf_jobs.txt; : > $J
for t in $LT; do AB=$($PY -c "import json;print(json.load(open('$CH'))['$t']['choice'].replace(',',':'))")
  BI=$($PY -c "import json;print(json.load(open('$D/dev/selection.json'))['info_t$t']['choice'])"); BR=$($PY -c "import json;print(json.load(open('$D/dev/selection.json'))['raw_t$t']['choice'])")
  for fl in $FLS; do F="--light RL-H:$t --fleet PL:$P/L11_${fl}_fleet.pt"
    echo "R_t${t}_$fl none none scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
    echo "TSI2_t${t}_$fl none none $(N4 $t) $F --light-obs q:$AB" >> $J
    echo "DCAS_t${t}_$fl info $D/tune_info/dcas_info_t${t}_b$BI.pt $(N4 $t) $F" >> $J
    echo "DCAR_t${t}_$fl raw $D/tune_raw/dcas_raw_t${t}_b$BR.pt $(N4 $t) $F" >> $J; done; done
xargs -P 6 -L 1 bash -c 'T=$0; M=$1; PP=$2; shift 2; [ -f $D/conf/$T.json ] && exit 0; if [ "$M" = none ]; then nice -n 5 $RUN "$@" --seeds '"$CS"' $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1; else DCAS_MODE=$M DCAS_END=$END DCAS_PARAMS=$PP nice -n 5 $RUN scripts/CITY_w12_dcas.py "$@" --seeds '"$CS"' $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1; fi || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation failed: stop"; exit 1; }
echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W12_SMOKE=$D W12_SEED=860 $PY scripts/CITY_w12_dcas_report.py; else $PY scripts/CITY_w12_dcas_report.py; fi || exit 1; echo "W12-DCAS done $(date)"
