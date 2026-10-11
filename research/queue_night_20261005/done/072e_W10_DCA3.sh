#!/usr/bin/env bash
# W10-1 DCA3 (PROTOCOL_CITY_WAVE10_20261005): corrected DC-Ada port (CITY_dca3_run.py + CITY_w7_dca3_tune.py, audit code reviewed 20:05) ->
# KW10-1 identity -> tuning at budget 176 (registered) and 704 (secondary), 5 lights in parallel -> fresh traffic 840-859 -> confirmation
# (R, TSI2, DCA3, DCA3X4 x t4-t8 x s213-s513 x 20) -> report.  SMOKE=1: DCA3_SMOKE budget 9 / 600 s, t4 x s213, seed 660, into W10_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W10_DIR:-research/city_sim/w10_20261005/dca3}; mkdir -p $D/check $D/tune $D/tune4 $D/conf; export XPLAY_TMP=$(cd $D/check && pwd)
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py
P=research/city_sim/spat_pilot_20261004/fleets_v11; TB=research/city_sim/f1b_20261004/prep; MOD=research/city_sim/tsi_20261005/cmodel/c2
CH=research/city_sim/tsi2_20261005/tune/choice.json; RUN="$PY -u scripts/CITY_f1a1_run.py"; echo "W10-DCA3 start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; export DCA3_SMOKE=1; LTS="4"; FLS="s213"; CS="660"; else SM=""; LTS="4 5 6 7 8"; FLS="s213 s313 s413 s513"; CS="$(seq -s ' ' 840 859)"; fi
# KW10-1: the DCA3 wrapper with the initial (identity) parameters == the plain service-only row
$PY -c "
import sys, torch; sys.path.insert(0, '.')
import scripts.CITY_dca3_run as R3, scripts.CITY_q7_cross_version as Q7
torch.save(R3.initial_params(sorted(Q7.NetInfo(Q7.NET_S).tls)), '$D/check/ident.pt')" || exit 1
F="--light RL-H:4 --fleet PL:$P/L11_s213_fleet.pt"; N4="--n4 0.5:hyb:$TB/prov_rlh4_cl.json:$MOD/n2_k4.pt"
[ -f $D/check/K_HYB.json ] || $RUN scripts/CITY_eval_n4.py $N4 $F --seeds 660 --smoke --tag K_HYB --out $D/check >> $D/check/run.log 2>&1 || exit 1
[ -f $D/check/K_ID.json ] || DCA3_PARAMS=$D/check/ident.pt $RUN scripts/CITY_dca3_run.py scripts/CITY_eval_n4.py $N4 $F --seeds 660 --smoke --tag K_ID --out $D/check >> $D/check/run.log 2>&1 || exit 1
$PY - <<PYC || { echo "KW10-1 FAIL: stop"; exit 1; }
import json, sys
a = json.load(open('$D/check/K_HYB.json'))['rows'][0]; b = json.load(open('$D/check/K_ID.json'))['rows'][0]; Q = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'fuel', 'teleports', 'unfinished')
ok = all(a[q] == b[q] for q in Q); t = f'KW10-1 identity DCA3 transform == HYB (smoke seed 660, t4, s213): {ok}\nKW10-1: {"PASS" if ok else "FAIL"}\n'; open('$D/check/kw10_1.txt', 'w').write(t); print(t); sys.exit(0 if ok else 1)
PYC
# tuning (fresh directories; the tuner refuses to reuse a finished one)
for t in $LTS; do [ -f $D/tune/dca3_t$t.json ] || nice -n 5 $PY -u scripts/CITY_w7_dca3_tune.py $t $D/tune > $D/tune/tune_t$t.log 2>&1 & done; wait
for t in $LTS; do [ -f $D/tune/dca3_params_t$t.pt ] || { echo "DCA3 tuning failed t$t: stop"; tail -3 $D/tune/tune_t$t.log; exit 1; }; done; echo "DCA3 tuning done $(date)"
for t in $LTS; do [ -f $D/tune4/dca3_t$t.json ] || nice -n 5 $PY -u scripts/CITY_w10_dca3x4.py $t $D/tune4 > $D/tune4/tune_t$t.log 2>&1 & done; wait
for t in $LTS; do [ -f $D/tune4/dca3_params_t$t.pt ] || { echo "DCA3x4 tuning failed t$t: stop"; tail -3 $D/tune4/tune_t$t.log; exit 1; }; done; echo "DCA3x4 tuning done $(date)"
unset DCA3_SMOKE
# fresh confirmation traffic 840-859
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF840_generated ]; then for s in $(seq 840 859); do [ -f $G/rou_s$s.xml ] && { echo "KW-0 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 840 859); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; date > $G/CONF840_generated; fi
J=$D/conf_jobs.txt; : > $J
for t in $LTS; do AB=$($PY -c "import json;print(json.load(open('$CH'))['$t']['choice'].replace(',',':'))"); N4="--n4 0.5:hyb:$TB/prov_rlh${t}_cl.json:$MOD/n2_k$t.pt"
  for fl in $FLS; do F="--light RL-H:$t --fleet PL:$P/L11_${fl}_fleet.pt"
    echo "R_t${t}_${fl} none scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "TSI2_t${t}_${fl} none scripts/CITY_eval_n4.py $N4 $F --light-obs q:$AB" >> $J
    echo "DCA3_t${t}_${fl} $D/tune/dca3_params_t$t.pt scripts/CITY_dca3_run.py scripts/CITY_eval_n4.py $N4 $F" >> $J
    echo "DCA3X4_t${t}_${fl} $D/tune4/dca3_params_t$t.pt scripts/CITY_dca3_run.py scripts/CITY_eval_n4.py $N4 $F" >> $J; done; done
export PY D RUN SM SS="$CS"
xargs -P 6 -L 1 bash -c 'T=$0; PP=$1; shift; [ -f $D/conf/$T.json ] && exit 0; if [ "$PP" = none ]; then nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1; else DCA3_PARAMS=$PP nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1; fi || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation failure: stop"; exit 1; }
echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W10_SMOKE=$(dirname $D) W10_SEED=660 $PY scripts/CITY_w10_report.py dca3; else $PY scripts/CITY_w10_report.py dca3; fi || exit 1; echo "W10-DCA3 done $(date)"
