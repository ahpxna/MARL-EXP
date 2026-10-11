#!/usr/bin/env bash
# W6-1 DCA (PROTOCOL_CITY_WAVE6_20261005): traffic 760-779 -> KW1-1 -> DC-Ada tuning per light (5 x 44 rollouts) -> confirmation (60 jobs x 20 seeds) -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/w6_20261005/dca; mkdir -p $D/check $D/tune $D/conf; export XPLAY_TMP=$PWD/$D/check
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; P=research/city_sim/spat_pilot_20261004/fleets_v11; TB=research/city_sim/f1b_20261004/prep
MOD=research/city_sim/tsi_20261005/cmodel/c2; CH=research/city_sim/tsi2_20261005/tune/choice.json; RUN="$PY -u scripts/CITY_f1a1_run.py"; echo "W6-DCA start $(date)"
if [ ! -f $G/CONF760_generated ]; then for s in $(seq 760 779); do [ -f $G/rou_s$s.xml ] && { echo "KW-0 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 760 779); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; date > $G/CONF760_generated; fi
echo "traffic 760-779 ready $(date)"
# KW1-1: affine theta = 0 == HYB (smoke seed 660, t4)
echo '{"s":[0,0,0,0,0,0,0],"b":[0,0,0,0,0,0,0]}' > $D/check/zero.json; F="--light RL-H:4 --fleet PL:$P/L11_s13_fleet.pt"; N4="--n4 0.5:hyb:$TB/prov_rlh4_cl.json:$MOD/n2_k4.pt"
[ -f $D/check/K_HYB.json ] || $RUN scripts/CITY_eval_n4.py $N4 $F --seeds 660 --smoke --tag K_HYB --out $D/check >> $D/check/run.log 2>&1
[ -f $D/check/K_AFF0.json ] || $RUN scripts/CITY_eval_n4.py $N4 $F --light-obs affine:$D/check/zero.json --seeds 660 --smoke --tag K_AFF0 --out $D/check >> $D/check/run.log 2>&1
$PY - <<PYC || { echo "KW1-1 FAIL: stop"; exit 1; }
import json, sys
a = json.load(open('$D/check/K_HYB.json'))['rows'][0]; b = json.load(open('$D/check/K_AFF0.json'))['rows'][0]; Q = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'fuel', 'teleports', 'unfinished')
ok = all(a[q] == b[q] for q in Q); t = f'KW1-1 affine theta=0 == HYB (smoke seed 660, t4): {ok}\nKW1-1: {"PASS" if ok else "FAIL"}\n'; open('$D/check/kw1_1.txt', 'w').write(t); print(t); sys.exit(0 if ok else 1)
PYC
printf "4\n5\n6\n7\n8\n" | xargs -P 5 -I{} bash -c "nice -n 5 $PY -u scripts/CITY_w6_dca_tune.py {} $D/tune > $D/tune/tune_t{}.log 2>&1 || echo 'FAIL dca tune {}'"
for t in 4 5 6 7 8; do [ -f $D/tune/affine_t$t.json ] || { echo "KW1-2 FAIL: no tuned transform for t$t"; exit 1; }; done; echo "DCA tuning done $(date)"
J=$D/conf_jobs.txt; : > $J; FLS=(s213 s313 s413 s513)
for t in 4 5 6 7 8; do AB=$($PY -c "import json;print(json.load(open('$CH'))['$t']['choice'].replace(',',':'))"); N4="--n4 0.5:hyb:$TB/prov_rlh${t}_cl.json:$MOD/n2_k$t.pt"
  for fl in ${FLS[@]}; do F="--light RL-H:$t --fleet PL:$P/L11_${fl}_fleet.pt"
    echo "R_t${t}_${fl} scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "TSI2_t${t}_${fl} scripts/CITY_eval_n4.py $N4 $F --light-obs q:$AB" >> $J
    echo "DCA_t${t}_${fl} scripts/CITY_eval_n4.py $N4 $F --light-obs affine:$D/tune/affine_t$t.json" >> $J; done; done
export PY D RUN SS="$(seq -s ' ' 760 779)"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || echo "FAIL $T"' < $J
echo "panel done $(date)"; $PY scripts/CITY_w6_report.py dca; echo "W6-DCA done $(date)"
