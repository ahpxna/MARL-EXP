#!/usr/bin/env bash
# W15-3b (PROTOCOL_CITY_WAVE15_20261007, Amendment A3): online calibration under model shift.  Krauss-calibrated FRESH2 providers in an
# IDM world (CITY_w13_idm): every arm on every day (fresh days 1200-1239, fleet s1013, lights t14-t18) -> CITY_w15_online choose (safe
# successive elimination, sees only the played arm's rows) -> every arm on fresh IDM evaluation traffic 1240-1259 (all fleets, HBEFA4 /
# PHEMlight5) -> report (descriptive).  SMOKE=1: t14, days 700-705 (existing grid4 seeds), eval 860, 600 s.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W15_DIR:-research/city_sim/w15_20261007}/online; F2=research/city_sim/w8_20261005/fresh2; G=research/city_sim/demand/grid4
RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; mkdir -p $D/days $D/eval $D/check; export XPLAY_TMP=$(cd $D/check && pwd); echo "W15-ONLINE start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="14"; FS="1013"; DS="$(seq -s ' ' 700 705)"; ES="860"; else SM=""; LT="14 15 16 17 18"; FS="1013 1113 1213 1313"; DS="$(seq -s ' ' 1200 1239)"; ES="$(seq -s ' ' 1240 1259)"; fi
gen() { [ "${SMOKE:-0}" = 1 ] && return 0; [ -f $G/CONF${1%% *}_generated ] && return 0
  for s in $1; do [ -f $G/rou_s$s.xml ] && { echo "KW15-3b FAIL: rou_s$s existed"; exit 1; }; done
  for s in $1; do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF${1%% *}_generated; echo "traffic ${1%% *}+ generated $(date)"; }
ARM() { case $1 in A1) echo "1:0.25 0.1";; A2) echo "1:0.5 0.1";; A3) echo "1.5:0 0.1";; A4) echo "1:0.25 0.5";; A5) echo "1:0.5 0.5";; esac; }
run_jobs() { export PY SM; export OUT=$2 SS="$3"
  xargs -P 6 -L 1 bash -c 'T=$0; X=$1; shift; [ -f $OUT/$T.json ] && exit 0; [ "$X" = P5 ] && export W13_EM=PHEMlight5/PC_EU4_G; nice -n 5 $PY -u scripts/CITY_w13_idm.py scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
gen "$DS"; gen "$ES"
J=$D/days_jobs.txt; : > $J
for k in $LT; do F="--light RL-H:$k --fleet PL:$F2/fleets/L11_s1013_fleet.pt"; echo "OFF_t$k H4 scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  for a in A1 A2 A3 A4 A5; do read AB Q <<< "$(ARM $a)"; echo "${a}_t$k H4 scripts/CITY_eval_n4.py --n4 $Q:hyb:$F2/prep/prov_rlh${k}_cl.json:$F2/cmodel/n2_k$k.pt $F --light-obs q:$AB" >> $J; done; done
run_jobs $J $D/days "$DS" || { echo "days failure: stop"; exit 1; }
W15_SMOKE=${SMOKE:-0} $PY scripts/CITY_w15_online.py choose $D || { echo "online choice FAIL"; exit 1; }
J=$D/eval_jobs.txt; : > $J
for k in $LT; do for s in $FS; do F="--light RL-H:$k --fleet PL:$F2/fleets/L11_s${s}_fleet.pt"
  for X in H4 P5; do x=""; [ "$X" = P5 ] && x=P5; echo "OFF${x}_t${k}_s$s $X scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
    for a in A1 A2 A3 A4 A5; do read AB Q <<< "$(ARM $a)"; echo "${a}${x}_t${k}_s$s $X scripts/CITY_eval_n4.py --n4 $Q:hyb:$F2/prep/prov_rlh${k}_cl.json:$F2/cmodel/n2_k$k.pt $F --light-obs q:$AB" >> $J; done; done; done; done
run_jobs $J $D/eval "$ES" || { echo "evaluation failure: stop"; exit 1; }
W15_SMOKE=${SMOKE:-0} $PY scripts/CITY_w15_online.py report $D || { echo "report FAIL"; exit 1; }
echo "W15-ONLINE done $(date)"
