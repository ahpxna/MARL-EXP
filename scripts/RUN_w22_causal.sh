#!/usr/bin/env bash
# W22 (PROTOCOL_CITY_WAVE22_20261017): SWB (switchback per light, 300 s, p 0.5) and MIX (per-vehicle, p 0.5) arms with the probe, families
# RMP (t94-98, W20), AH (t34-38, W19), RWV (t99-103, W20), fleets FRESH3 s1413 / s1513, days 1400-1409, grid4 W20 setting -> CITY_w22_report.py.
# KW22-1 / KW22-2 (identity) are run first by this script (skipped if their rows exist).  Re-running skips complete rows.
# SMOKE=1: RMP t94, s1413, day 1400, --smoke, into .../smoke; report with W22_SMOKE=1.
set -o pipefail; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W22_PROBE=1
PY=external_envs/city_runtime/bin/python; F3=research/city_sim/w15_20261007/fresh3/fleets; W19=research/city_sim/w19_20261008; W20=research/city_sim/w20_20261009
if [ "${SMOKE:-0}" = 1 ]; then E=research/city_sim/w22_20261017/smoke; FAMS="RMP:94-94:w20"; FS="1413"; DAYS="1400"; SM="--smoke"
else E=research/city_sim/w22_20261017/panel; FAMS="RMP:94-98:w20 AH:34-38:w19 RWV:99-103:w20"; FS="1413 1513"; DAYS="1400 1401 1402 1403 1404 1405 1406 1407 1408 1409"; SM=""; fi
mkdir -p $E; echo "W22 start $(date); dir $E; $(pmset -g batt | sed -n 2p | cut -c1-60)"
echo "sources: $(shasum -a 256 scripts/CITY_w22_assign.py scripts/CITY_w22_report.py scripts/CITY_eval_n4.py scripts/CITY_eval_f1.py scripts/CITY_w20_run.py scripts/CITY_w9_run.py scripts/CITY_fleet_v11.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
export PY E SM DAYS; export M="$PY -u scripts/CITY_w9_run.py none scripts/CITY_w20_run.py scripts/CITY_w22_assign.py"
J=$E/jobs.txt; : > $J
for f in $FAMS; do n=${f%%:*}; r=${f#*:}; r=${r%%:*}; src=${f##*:}; P=$W20; [ $src = w19 ] && P=$W19
  for k in $(seq ${r%-*} ${r#*-}); do for s in $FS; do A="--n4 0.1:hyb:$P/prep/prov_rlh${k}_cl.json:$P/cmodel/n2_k$k.pt --light RL-H:$k --fleet PL:$F3/L11_s${s}_fleet.pt"
    echo "SWB_t${k}_s$s swb:300:0.5 scripts/CITY_eval_n4.py $A" >> $J; echo "MIX_t${k}_s$s veh:0.5 scripts/CITY_eval_n4.py $A" >> $J; done; done; done
echo "jobs: $(wc -l < $J) x $(echo $DAYS | wc -w) days"
xargs -P ${LANES:-6} -L 1 bash -c 'T=$0; A=$1; shift; grep -qs "\"status\": \"COMPLETE\"" $E/$T.json && exit 0
  W22_ASSIGN=$A nice -n 5 $M "$@" --seeds $DAYS $SM --tag $T --out $E > $E/$T.log 2>&1 || echo "FAIL $T"' < $J
bad=0; while read -r T _; do grep -qs '"status": "COMPLETE"' $E/$T.json || { echo "INCOMPLETE $T"; bad=1; }; done < $J
[ $bad = 0 ] || { echo "panel incomplete: stop (re-run to resume)"; exit 1; }
echo "panel done $(date)"
W22_SMOKE=${SMOKE:-0} $PY scripts/CITY_w22_report.py $E "$FAMS" "$FS" "$DAYS" || { echo "report FAIL"; exit 1; }
echo "W22 done $(date)"
