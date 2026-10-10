#!/usr/bin/env bash
# W14-2 (PROTOCOL_CITY_WAVE14_20261007): the W9 perturbations (1-s delay, 20 / 50 % loss, 80 % detection, 1 m/s speed noise) applied to the
# W13 TSI (TRB) and the W8-2 TSI (TW8) on the W13 confirmation traffic 900-919 (FRESH2 t14-t18 x s1013-s1313); R and the unperturbed arms
# are the W13 rows.  HBEFA4.  Report CITY_w14_robust_report.  SMOKE=1: t14 x s1013, seed 860, 600 s, against the W13 smoke rows in W14_W13CONF.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
B=${W14_DIR:-research/city_sim/w14_20261007}; D=$B/robust; F2=research/city_sim/w8_20261005/fresh2; W13=${W14_W13:-research/city_sim/w13_20261006}
mkdir -p $D $B/check; export XPLAY_TMP=$(cd $B/check && pwd); echo "W14-ROBUST start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LT="14"; FS="1013"; CS="860"; else SM=""; LT="14 15 16 17 18"; FS="1013 1113 1213 1313"; CS="$(seq -s ' ' 900 919)"; fi
[ -f $W13/tune/choice_RB.json ] || { echo "W13 choice missing: stop"; exit 1; }
CH() { $PY -c "import json;c=json.load(open('$1'))['$2']['choice'].split(',');print(c[0]+':'+c[1]+' '+(c[2] if len(c)>2 else '0.5'))"; }
J=$D/jobs.txt; : > $J
for k in $LT; do read W8AB W8Q <<< "$(CH $F2/tune/choice.json $k)"; read RAB RQ <<< "$(CH $W13/tune/choice_RB.json $k)"
  for s in $FS; do F="--light RL-H:$k --fleet PL:$F2/fleets/L11_s${s}_fleet.pt"
    for mm in LAT1:lat:1 LOSS20:loss:0.2 LOSS50:loss:0.5 DET80:det:0.8 SPN1:spn:1; do m=${mm%%:*}; mode=${mm#*:}
      echo "TRB${m}_t${k}_s$s $mode scripts/CITY_eval_n4.py --n4 $RQ:hyb:$F2/prep/prov_rlh${k}_cl.json:$F2/cmodel/n2_k$k.pt $F --light-obs q:$RAB" >> $J
      echo "TW8${m}_t${k}_s$s $mode scripts/CITY_eval_n4.py --n4 0.5:hyb:$F2/prep/prov_rlh${k}_cl.json:$F2/cmodel/n2_k$k.pt $F --light-obs q:$W8AB" >> $J; done; done; done
export PY D SM; export SS="$CS"
xargs -P 6 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $D/$T.json ] || nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_w13_modes.py "$@" --seeds $SS $SM --tag $T --out $D >> $D/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "robustness failure: stop"; exit 1; }
if [ "${SMOKE:-0}" = 1 ]; then W14_SMOKE=1 W14_SEED=860 W14_W13CONF=$W13/conf $PY scripts/CITY_w14_robust_report.py $B; else $PY scripts/CITY_w14_robust_report.py $B; fi || { echo "report FAIL"; exit 1; }
echo "W14-ROBUST done $(date)"
