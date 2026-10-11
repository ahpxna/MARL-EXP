#!/usr/bin/env bash
# W11 FoRL (PROTOCOL_CITY_WAVE11_FORL_20261005 + A1): waits for the running DCA3 job (072e) -> trains FoRL lights s1-s5 (200 episodes, the authors'
# tls settings) -> fresh grid4 traffic 860-879 -> R_F / FORL (FoRL lights) and R / TSI2 (RL-H t4-t8) x fleets s213-s513, HUM_F / HUM_R (SUMO
# drivers) -> KF11-1 (yellow-branch exactness, served answers, s1 x s213 x TUNE 660) -> report.  SMOKE=1: 2 x 300-s episodes, s1 / t4 / s213,
# seed 660, 600 s, into W11_DIR (no wait).
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W11_DIR:-research/city_sim/w11_20261005/forl}; mkdir -p $D/lights $D/conf $D/check; export XPLAY_TMP=$(cd $D/check && pwd)
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py
P=research/city_sim/spat_pilot_20261004/fleets_v11; TB=research/city_sim/f1b_20261004/prep; MOD=research/city_sim/tsi_20261005/cmodel/c2
CH=research/city_sim/tsi2_20261005/tune/choice.json; RUN="$PY -u scripts/CITY_f1a1_run.py"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; EP=2; LS="1"; LT="4"; FLS="s213"; CS="660"
else SM=""; EP=200; LS="1 2 3 4 5"; LT="4 5 6 7 8"; FLS="s213 s313 s413 s513"; CS="$(seq -s ' ' 860 879)"
  W=$(pgrep -f "running/072e_W10_DCA3.sh" | head -1); [ -n "$W" ] && { echo "waiting for DCA3 (pid $W) $(date)"; caffeinate -w $W; }; fi
echo "W11-FORL start $(date)"
for s in $LS; do [ -f $D/lights/FORL_s$s.pt ] || nice -n 5 $PY -u scripts/CITY_forl.py --seed $s --episodes $EP --name FORL_s$s --out $D/lights $SM > $D/lights/train_s$s.out 2>&1 & done; wait
for s in $LS; do [ -f $D/lights/FORL_s$s.pt ] || { echo "FoRL training failed s$s"; tail -3 $D/lights/train_s$s.out; exit 1; }; done; echo "FoRL lights done $(date)"
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF860_generated ]; then for s in $(seq 860 879); do [ -f $G/rou_s$s.xml ] && { echo "KW11-0 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 860 879); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; date > $G/CONF860_generated; fi
# KF11-1: yellow-branch exactness of the published FoRL forecast (served answers)
F1=$(echo $FLS | cut -d' ' -f1)
W10_LOG=$D/check/served $PY -u scripts/CITY_w10_run.py serve scripts/CITY_eval_forl.py --forl-spat on --light FORL:$D/lights/FORL_s1.pt --fleet PL:$P/L11_${F1}_fleet.pt --seeds 660 --smoke --record $D/check/rec/KF_s{seed}.npz --tag KF --out $D/check > $D/check/kf.log 2>&1 || { echo "KF run FAIL"; exit 1; }
$PY scripts/CITY_w11_check.py $D/check/served/KF_served_s660.npz $D/check/rec/KF_s660.npz | tee $D/check/kf11_1.txt || { echo "KF11-1 FAIL: stop"; exit 1; }
J=$D/conf_jobs.txt; : > $J
for s in $LS; do echo "HUM_s$s scripts/CITY_eval_forl.py --forl-spat off --light FORL:$D/lights/FORL_s$s.pt --fleet human" >> $J
  for fl in $FLS; do F="--light FORL:$D/lights/FORL_s$s.pt --fleet PL:$P/L11_${fl}_fleet.pt"
    echo "R_F_s${s}_${fl} scripts/CITY_eval_forl.py --forl-spat off $F" >> $J; echo "FORL_s${s}_${fl} scripts/CITY_eval_forl.py --forl-spat on $F" >> $J; done; done
for t in $LT; do AB=$($PY -c "import json;print(json.load(open('$CH'))['$t']['choice'].replace(',',':'))"); N4="--n4 0.5:hyb:$TB/prov_rlh${t}_cl.json:$MOD/n2_k$t.pt"
  echo "HUM_R_$t scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$t --fleet human" >> $J
  for fl in $FLS; do F="--light RL-H:$t --fleet PL:$P/L11_${fl}_fleet.pt"
    echo "R_${t}_${fl} scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "TSI2_${t}_${fl} scripts/CITY_eval_n4.py $N4 $F --light-obs q:$AB" >> $J; done; done
sed -i '' 's/^HUM_s/HUM_F_s/' $J
export PY D RUN SM SS="$CS"
xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation failure: stop"; exit 1; }
echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W11_SMOKE=$D W11_SEED=660 $PY scripts/CITY_w11_report.py; else $PY scripts/CITY_w11_report.py; fi || exit 1; echo "W11-FORL done $(date)"
