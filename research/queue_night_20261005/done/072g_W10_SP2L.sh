#!/usr/bin/env bash
# W10-4 SPIDER-2L (PROTOCOL_CITY_WAVE10_20261005, Amendment A2): the spider TSI pipeline from scratch on the 2-lane spider build.
# demand -> RLK lights 11 / 111 (120 ep) -> P1 light check, P2 rule-fleet benefit (DEV 100-104) -> sigma* traces -> open-loop table ->
# closed-loop table -> N2K logs -> fit -> KS-1 / KS-2 -> tuning (TUNE 1100-1103) -> confirmation (1110-1129) -> report.
# SMOKE=1: 1-episode lights, 600 s runs, one TUNE / conf seed, into W10_DIR (demand into the smoke dir).
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W10_DIR:-research/city_sim/w10_20261005/sp2l}; mkdir -p $D/lights $D/check $D/traces $D/prov $D/data $D/model $D/tune $D/conf $D/pre; export XPLAY_TMP=$(cd $D/check && pwd)
NET=research/city_sim/net/spider2l.net.xml; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py
RUN="$PY -u scripts/CITY_sp2l_run.py"; EV="$RUN scripts/CITY_m4s_tsi_eval.py"; echo "W10-SP2L start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LEP=1; DEVS="100"; TUN="1100"; CONF="1110"; G=$D/demand; export W10_TUNE_SEEDS=1100
else SM=""; LEP=120; DEVS="100 101 102 103 104"; TUN="1100 1101 1102 1103"; CONF="$(seq -s ' ' 1110 1129)"; G=research/city_sim/demand/spider2l/p2.0; fi
[ "$(shasum -a 256 $NET | cut -c1-16)" = 291d6a0c70f53c72 ] || { echo "KW10-4 net hash mismatch: stop"; exit 1; }
# demand: generated once after a non-existence check (marker = generated); the runner and trainer read $G through W10_SP2L_ROU
export W10_SP2L_ROU="$(cd $(dirname $G) 2>/dev/null && pwd)/$(basename $G)/rou_s{}.xml"; mkdir -p $G; export W10_SP2L_ROU="$(cd $G && pwd)/rou_s{}.xml"
if [ ! -f $G/generated ]; then for s in 0 1 2 3 4 5 6 7 $DEVS $TUN $CONF; do [ -f $G/rou_s$s.xml ] && { echo "KW10-4 FAIL: rou_s$s existed"; exit 1; }; done
  for s in 0 1 2 3 4 5 6 7 $DEVS $TUN $CONF; do $PY $RT -n $NET -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/generated; fi
echo "demand ready $(date)"
# 1. RLK lights
for k in 11 111; do [ -f $D/lights/RLK2L_sp$k.pt ] || nice -n 5 $PY -u scripts/CITY_m4g_train_light.py --net $NET --rou "$W10_SP2L_ROU" --seed $k --episodes $LEP --name RLK2L_sp$k --out $D/lights $SM > $D/lights/train_$k.out 2>&1 & done; wait
for k in 11 111; do [ -f $D/lights/RLK2L_sp$k.pt ] || { echo "light training failed $k"; tail -3 $D/lights/train_$k.out; exit 1; }; done; echo "lights done $(date)"
# 2. preconditions P1 (learned light vs FT, SUMO drivers) and P2 (rule fleet vs sigma* under FT)
J=$D/pre_jobs.txt; : > $J
echo "FT_h scripts/CITY_m4s_tsi_eval.py --tk none --light FT" >> $J; for k in 11 111; do echo "RLK${k}_h scripts/CITY_m4s_tsi_eval.py --tk none --light RLK:$D/lights/RLK2L_sp$k.pt" >> $J; done
echo "GLOSAL_FT scripts/CITY_eval6_lane.py --light FT --fleet GLOSAL:0.3" >> $J; echo "SIG_FT scripts/CITY_eval4_sigma.py --sigma 0.3 --light FT --fleet L-ACT:0 --guard always" >> $J
export PY D RUN SM DEVS; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/pre/$T.json ] || nice -n 5 $RUN "$@" --seeds $DEVS $SM --tag $T --out $D/pre >> $D/pre/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "precondition runs failed: stop"; exit 1; }
# 3. sigma* traces (rule fleet without SPaT = sigma*) -> open-loop table; closed-loop table
for k in 11 111; do [ -f $D/traces/ol_k$k.json ] || nice -n 5 $EV --tk none --light RLK:$D/lights/RLK2L_sp$k.pt --fleet GLOSAL:0.3 --seeds 0 1 2 3 4 5 6 7 $SM --record $D/traces/ol_k${k}_s{seed}.npz --tag ol_k$k --out $D/traces >> $D/traces/run.log 2>&1 & done; wait
fitk() { $PY -c "
import sys, json; sys.path.insert(0, '.')
import scripts.CITY_sp2l_run, scripts.CITY_spat_forecast_k as FK
T = FK.fit_k(['$1_s%d.npz' % s for s in range(8)]); json.dump(T, open('$2', 'w')); print('fit', '$2', 'lights', len(T['per']), 'files', T['n_files'])"; }
for k in 11 111; do [ -f $D/prov/fk_k$k.json ] || fitk $D/traces/ol_k$k $D/prov/fk_k$k.json || { echo "open-loop fit FAIL $k"; exit 1; }; done
for k in 11 111; do [ -f $D/traces/cl_k$k.json ] || nice -n 5 $EV --tk fk:0.5:$D/prov/fk_k$k.json --light RLK:$D/lights/RLK2L_sp$k.pt --fleet GLOSAL:0.3 --seeds 0 1 2 3 4 5 6 7 $SM --record $D/traces/cl_k${k}_s{seed}.npz --tag cl_k$k --out $D/traces >> $D/traces/run.log 2>&1 & done; wait
for k in 11 111; do [ -f $D/prov/fkcl_k$k.json ] || fitk $D/traces/cl_k$k $D/prov/fkcl_k$k.json || { echo "closed-loop fit FAIL $k"; exit 1; }; done
# 4. N2K logs, fit, KS-1 / KS-2
J=$D/collect.txt; : > $J; for k in 11 111; do for s in 0 1 2 3 4 5 6 7; do echo "$k $s" >> $J; done; done; export EV
xargs -P 6 -L 1 bash -c '[ -f $D/data/k$0/feat_s$1.npz ] || nice -n 5 $EV --tk fk:0.1:$D/prov/fkcl_k$0.json --light RLK:$D/lights/RLK2L_sp$0.pt --fleet GLOSAL:0.3 --featlog $D/data/k$0 --seeds $1 $SM --tag C_k$0_s$1 --out $D/data/k$0 >> $D/data/run.log 2>&1 || { echo "FAIL collect $0 $1"; exit 255; }' < $J || { echo "collection failed: stop"; exit 1; }
for k in 11 111; do [ -f $D/model/n2k_k$k.pt ] || $RUN scripts/CITY_n2k.py fit $D/data/k$k $D/model/n2k_k$k.pt > $D/model/fit_k$k.log 2>&1 || { echo "N2K fit FAIL $k"; tail -3 $D/model/fit_k$k.log; exit 1; }; done
TK11="n2k:$D/prov/fkcl_k11.json:$D/model/n2k_k11.pt"
$EV --tk $TK11 --light RLKQ:$D/lights/RLK2L_sp11.pt:2:0 --fleet GLOSAL:0.3 --featlog $D/check/ks1 --seeds 0 --smoke --tag KS1 --out $D/check > $D/check/ks1.log 2>&1 || { echo "KS1 run FAIL"; exit 1; }
$RUN scripts/CITY_n2k.py parity $D/check/ks1 0 $D/model/n2k_k11.pt | tee $D/check/ks1_parity.txt || { echo "KS-1 FAIL: stop"; exit 1; }
$PY -c "import json;x=json.load(open('$D/check/KS1_tk.json'));p=x['provider'];print('KS-2', p);raise SystemExit(0 if p['n2k']>0 and p['fk_direct']>0 and p['exc']==0 else 1)" || { echo "KS-2 FAIL"; exit 1; }
# 5. tuning
J=$D/tune_jobs.txt; : > $J
for k in 11 111; do TK="n2k:$D/prov/fkcl_k$k.json:$D/model/n2k_k$k.pt"; L=$D/lights/RLK2L_sp$k.pt; echo "R_$k --tk none --light RLK:$L --fleet GLOSAL:0.3" >> $J
  for ab in "0 0" "1 0" "2 0" "1 0.25" "1.5 0.25" "1 0.5" "2 0.5"; do set -- $ab; T=$(echo "T_${k}_a$1_b$2" | tr '.' 'p'); echo "$T --tk $TK --light RLKQ:$L:$1:$2 --fleet GLOSAL:0.3" >> $J; done; done
export TUN; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/tune/$T.json ] || nice -n 5 $EV "$@" --seeds $TUN $SM --tag $T --out $D/tune >> $D/tune/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "tuning failed: stop"; exit 1; }
$PY scripts/CITY_w10_sp2l_tune.py $D | tee $D/tune/tune.txt || { echo "TUNE FAIL"; exit 1; }
# 6. confirmation
J=$D/conf_jobs.txt; : > $J
for k in 11 111; do AB=$($PY -c "import json;print(json.load(open('$D/tune/choice.json'))['$k']['choice'].replace(',',':'))"); TK="n2k:$D/prov/fkcl_k$k.json:$D/model/n2k_k$k.pt"; L=$D/lights/RLK2L_sp$k.pt
  echo "R_$k --tk none --light RLK:$L --fleet GLOSAL:0.3" >> $J; echo "TSIK_$k --tk $TK --light RLKQ:$L:$AB --fleet GLOSAL:0.3" >> $J
  echo "HYBK_$k --tk $TK --light RLK:$L --fleet GLOSAL:0.3" >> $J; echo "ADPK_$k --tk none --light RLKQ:$L:$AB --fleet GLOSAL:0.3" >> $J; done
export CONF; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $EV "$@" --seeds $CONF $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation failed: stop"; exit 1; }
echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W10_SMOKE=$(dirname $D) $PY scripts/CITY_w10_sp2l_report.py; else $PY scripts/CITY_w10_sp2l_report.py; fi || exit 1; echo "W10-SP2L done $(date)"
