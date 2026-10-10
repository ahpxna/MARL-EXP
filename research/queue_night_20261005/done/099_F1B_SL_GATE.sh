#!/usr/bin/env bash
# F1 gate re-run on the CORRECTED programs (PROTOCOL_CITY_F1_SALTLAKE_20261008, Amendments A3 / A4): attempt 3 = RLK (grid4 recipe,
# 120 ep, alpha 0.0125) in gateK; attempt 4 = RLW (F1-B wide light, CITY_lightw, 240 ep, alpha 0.00625) in gateW (rows tagged RLK<k>_<site>
# so that CITY_sl_gate_report is reused).  FT = the tuned plan (KSL-5: identical to v1).  All SUMO cars, 10 DEV days per site.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
B=${SL_DIR:-research/city_sim/f1_saltlake}; echo "F1B-SL-GATE start $(date)"
DAYS() { $PY -c "import sys; sys.path.insert(0,'.'); from scripts.CITY_sl_build import days; print(' '.join(str(d.timetuple().tm_yday) for d in days('$1','$2')))"; }
for v in K W; do D=$B/gate$v; mkdir -p $D/lights
  if [ $v = K ]; then RUNR=scripts/CITY_sl_run.py; TRN=scripts/CITY_sl_train_light.py; EP=120; SPEC=RLK; else RUNR=scripts/CITY_sl_runw.py; TRN=scripts/CITY_sl_train_lightw.py; EP=240; SPEC=RLW; fi
  for site in 400sX200w stateXuniversity; do TR="$(DAYS $site train)"; NET=research/city_sim/net/saltlake_$site.net.xml; ROU="research/city_sim/demand/saltlake/$site/rou_s{}.xml"
    for k in 11 12; do [ -f $D/lights/${SPEC}_${site}_$k.pt ] || SL_SITE=$site nice -n 5 $PY -u $RUNR $TRN --net $NET --rou "$ROU" --seed $k --episodes $EP --days $TR --name ${SPEC}_${site}_$k --out $D/lights > $D/lights/train_${site}_$k.out 2>&1 & done; done; done; wait
for v in K W; do D=$B/gate$v; if [ $v = K ]; then RUNR=scripts/CITY_sl_run.py; SPEC=RLK; else RUNR=scripts/CITY_sl_runw.py; SPEC=RLW; fi
  for site in 400sX200w stateXuniversity; do for k in 11 12; do [ -f $D/lights/${SPEC}_${site}_$k.pt ] || { echo "missing light $v $site $k: stop"; tail -3 $D/lights/train_${site}_$k.out; exit 1; }; done
    DV="$(DAYS $site dev)"
    [ -f $D/FT_$site.json ] || SL_SITE=$site nice -n 5 $PY -u $RUNR scripts/CITY_m4s_tsi_eval.py --tk none --light FT --seeds $DV --tag FT_$site --out $D >> $D/run.log 2>&1 &
    for k in 11 12; do [ -f $D/RLK${k}_$site.json ] || SL_SITE=$site nice -n 5 $PY -u $RUNR scripts/CITY_m4s_tsi_eval.py --tk none --light $SPEC:$D/lights/${SPEC}_${site}_$k.pt --seeds $DV --tag RLK${k}_$site --out $D >> $D/run.log 2>&1 & done; done; done; wait
$PY scripts/CITY_sl_gate_report.py $B/gateK 0.0125 || { echo "report K FAIL"; exit 1; }
$PY scripts/CITY_sl_gate_report.py $B/gateW 0.00625 || { echo "report W FAIL"; exit 1; }
echo "F1B-SL-GATE done $(date)"
