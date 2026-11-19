#!/usr/bin/env bash
# W22-E (PROTOCOL_CITY_WAVE22_20261017, Amendment W22-E): grid4 MIX p 0.3 / 0.5 / 0.7 for SRL, RDQ; W17 MIX p 0.3 / 0.7 and NSW 600 s for RMP, AH,
# RWV; checks KW22-0 (grid4) and KW22-C1/C2 (W17) with the current wrapper; battery guard as RUN_w22abc.sh -> CITY_w22e_report.py.
# SMOKE=1: one cell per kind, one day, --smoke, into .../w22_20261017/smoke_e (checks skipped).
set -o pipefail; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W22_PROBE=1
PY=external_envs/city_runtime/bin/python; F3=research/city_sim/w15_20261007/fresh3/fleets; F5=research/city_sim/w17_20261008/fresh5/fleets
W19=research/city_sim/w19_20261008; W20=research/city_sim/w20_20261009; A17=research/city_sim/w21_20261015/w17; B=research/city_sim/w22_20261017
if [ "${SMOKE:-0}" = 1 ]; then O=$B/smoke_e; SM="--smoke"; GF="SRL:84-84"; GS="1413"; GD="1400"; WF="RMP:94-94"; WS="2213"; WD="1420"
else O=$B/e; SM=""; GF="SRL:84-88 RDQ:89-93"; GS="1413 1513"; GD="1400,1401,1402,1403,1404,1405,1406,1407,1408,1409"; WF="RMP:94-98 AH:34-38 RWV:99-103"; WS="2213 2313"; WD="1420,1421,1422,1423,1424,1425,1426,1427,1428,1429"; fi
mkdir -p $O/g4 $O/w17 $O/check $O/tmp; export XPLAY_TMP=$(cd $O/tmp && pwd) PY SM
echo "W22-E start $(date); out $O; $(pmset -g batt | sed -n 2p | cut -c1-60)"
echo "sources: $(shasum -a 256 scripts/CITY_w22_assign.py scripts/CITY_w22e_report.py scripts/CITY_eval_n4.py scripts/CITY_w20_run.py scripts/CITY_w9_run.py scripts/CITY_w13_modes.py scripts/CITY_w17_world.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
run_jobs() { xargs -P ${LANES:-6} -L 1 bash -c 'T=$0; A=$1; OUT=$2; DS=${3//,/ }; CHN=$4; shift 4
  grep -qs "\"status\": \"COMPLETE\"" $OUT/$T.json && exit 0
  b=$(pmset -g batt | grep -o "[0-9]*%" | head -1 | tr -d %); pmset -g batt | grep -q "discharging" && [ "$b" -le 20 ] && { echo "SKIP $T (battery $b%)"; exit 0; }
  if [ $CHN = w ]; then C="$PY -u scripts/CITY_w17_world.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py scripts/CITY_w13_modes.py scripts/CITY_w22_assign.py"
    export W20_LIGHTS=$(cd research/city_sim/w21_20261015/w17/lights && pwd) W19_LIGHTS=$(cd research/city_sim/w21_20261015/w17/lights && pwd) W7_FPR_DIR=$(cd research/city_sim/w21_20261015/w17 && pwd)
  else C="$PY -u scripts/CITY_w9_run.py none scripts/CITY_w20_run.py scripts/CITY_w22_assign.py"; fi
  W22_ASSIGN=$A nice -n 5 $C "$@" --seeds $DS $SM --tag $T --out $OUT > $OUT/$T.log 2>&1 || echo "FAIL $T"' < $1; }
complete() { local bad=0; while read -r T _ OUT _; do grep -qs '"status": "COMPLETE"' $OUT/$T.json || { echo "INCOMPLETE $T"; bad=1; }; done < $1; return $bad; }
n4() { local P=$W20; [ $1 -lt 84 ] && P=$W19; [ "$2" = w ] && P=$A17; echo "--n4 0.1:hyb:$P/prep/prov_rlh$1_cl.json:$P/cmodel/n2_k$1.pt"; }
same() { $PY - "$@" <<'PY'
import json, sys
a, b, days = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3].split(',')]; extra = sys.argv[4:]
F = ['timeloss', 'timeloss_agent', 'timeloss_human', 'fuel', 'fuel_agent', 'n', 'teleports', 'unfinished', 'action_digest', 'green_mean'] + extra
x = {r['seed']: r for r in json.load(open(a))['rows']}; y = {r['seed']: r for r in json.load(open(b))['rows']}
bad = [(d, f) for d in days for f in F if x[d].get(f) != y[d].get(f)]
print(('IDENTICAL ' if not bad else f'DIFFERENT {bad[:5]} ') + a.split('/')[-1] + ' vs ' + b.split('/')[-1]); sys.exit(1 if bad else 0)
PY
}
if [ "${SMOKE:-0}" != 1 ]; then J=$O/check/jobs.txt; : > $J
  for a in all none; do echo "K0_${a}_t94_s1413 $a $O/check 1400,1401 g scripts/CITY_eval_n4.py $(n4 94 g) --light RL-H:94 --fleet PL:$F3/L11_s1413_fleet.pt" >> $J
    echo "KC_${a}_t94_s2213 $a $O/check 1420,1421 w scripts/CITY_eval_n4.py $(n4 94 w) --light RL-H:94 --fleet PL:$F5/L11_s2213_fleet.pt" >> $J; done
  run_jobs $J; complete $J || { echo "checks incomplete: stop"; exit 1; }
  same $O/check/K0_all_t94_s1413.json $W20/conf/SV_t94_s1413.json 1400,1401 && same $O/check/K0_none_t94_s1413.json $W20/conf/R_t94_s1413.json 1400,1401 \
   && same $O/check/KC_all_t94_s2213.json $A17/conf/SV_t94_s2213.json 1420,1421 && same $O/check/KC_none_t94_s2213.json $A17/conf/R_t94_s2213.json 1420,1421 \
   || { echo "KW22-0 / KW22-C FAIL: stop"; exit 1; }; echo "KW22-0 and KW22-C1/C2 PASS"; fi
J=$O/jobs.txt; : > $J
for f in $GF; do r=${f#*:}; for k in $(seq ${r%-*} ${r#*-}); do for s in $GS; do X="scripts/CITY_eval_n4.py $(n4 $k g) --light RL-H:$k --fleet PL:$F3/L11_s${s}_fleet.pt"
  for p in 30 50 70; do echo "MIXp${p}_t${k}_s$s veh:0.${p%0} $O/g4 $GD g $X" >> $J; done; done; done; done
for f in $WF; do r=${f#*:}; for k in $(seq ${r%-*} ${r#*-}); do for s in $WS; do X="scripts/CITY_eval_n4.py $(n4 $k w) --light RL-H:$k --fleet PL:$F5/L11_s${s}_fleet.pt"
  for p in 30 70; do echo "MIXp${p}_t${k}_s$s veh:0.${p%0} $O/w17 $WD w $X" >> $J; done; echo "NSW_t${k}_s$s nsw:600:0.5 $O/w17 $WD w $X" >> $J; done; done; done
echo "W22-E jobs: $(wc -l < $J)"; run_jobs $J
if complete $J; then n=$(cat $O/w17/*.log | grep -o "KW17-0: type v_passenger tau" | wc -l); nj=$(grep -c " w scripts" $J); echo "KW17-0 lines: $n (W17 jobs $nj)"
  grep -qs "KW17-0 FAIL" $O/w17/*.log && echo "KW17-0 FAIL" || { [ $n -ge $nj ] && W22_SMOKE=${SMOKE:-0} $PY scripts/CITY_w22e_report.py $O "$GF" "$GS" "${GD//,/ }" "$WF" "$WS" "${WD//,/ }" || echo "W22-E report FAIL"; }
  echo "W22-E done $(date)"; else echo "W22-E incomplete (re-run)"; fi
