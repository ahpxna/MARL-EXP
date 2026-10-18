#!/usr/bin/env bash
# W22-F (PROTOCOL_CITY_WAVE22_20261017, Amendment W22-F): checks with the new wrapper CITY_w22f_assign.py, then F1 (same-day two shares),
# F3 (probe 2), F4 (Midtown area design), F2 (other W19 families) — order set on battery so the costliest-to-lose parts come first; battery guard; each part's report runs when its rows are complete.
# SMOKE=1: one cell per part, one day, --smoke, checks skipped, into .../w22_20261017/smoke_f.
set -o pipefail; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1
PY=external_envs/city_runtime/bin/python; F3=research/city_sim/w15_20261007/fresh3/fleets; F5=research/city_sim/w17_20261008/fresh5/fleets
W19=research/city_sim/w19_20261008; W20=research/city_sim/w20_20261009; A17=research/city_sim/w21_20261015/w17; B=research/city_sim/w22_20261017
if [ "${SMOKE:-0}" = 1 ]; then O=$B/smoke_f; SM="--smoke"; GD="1400"; WD="1420"; GS="1413"; WS="2213"; MD="0"; MS="1413"; KR="1"
else O=$B/f; SM=""; GD="1400,1401,1402,1403,1404,1405,1406,1407,1408,1409"; WD="1420,1421,1422,1423,1424,1425,1426,1427,1428,1429"; GS="1413 1513"; WS="2213 2313"; MD="0,1,2,3,4"; MS="1413 1513"; KR="5"; fi
G3D=$(echo $GD | cut -d, -f1-4); W3D=$(echo $WD | cut -d, -f1-4)
mkdir -p $O/check $O/g4 $O/w17 $O/f1/g4 $O/f1/w17 $O/f2 $O/mt $O/tmp; export XPLAY_TMP=$(cd $O/tmp && pwd) PY SM
echo "W22-F start $(date); out $O; $(pmset -g batt | sed -n 2p | cut -c1-60)"
echo "sources: $(shasum -a 256 scripts/CITY_w22f_assign.py scripts/CITY_w22f_report.py scripts/CITY_eval_n4.py scripts/CITY_w20_run.py scripts/CITY_w9_run.py scripts/CITY_w13_modes.py scripts/CITY_w17_world.py scripts/DEMO_midtown.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
# job line: <tag> <assign> <probe> <out dir> <days,> <chain g|w|m> <evaluator> <args>
run_jobs() { xargs -P ${LANES:-9} -L 1 bash -c 'T=$0; A=$1; PR=$2; OUT=$3; DS=${4//,/ }; CHN=$5; shift 5
  grep -qs "\"status\": \"COMPLETE\"" $OUT/$T.json && exit 0
  b=$(pmset -g batt | grep -o "[0-9]*%" | head -1 | tr -d %); pmset -g batt | grep -q "discharging" && [ "$b" -le 20 ] && { echo "SKIP $T (battery $b%)"; exit 0; }
  case $CHN in
    w) C="$PY -u scripts/CITY_w17_world.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py scripts/CITY_w13_modes.py scripts/CITY_w22f_assign.py"
       export W20_LIGHTS=$(cd research/city_sim/w21_20261015/w17/lights && pwd) W19_LIGHTS=$(cd research/city_sim/w21_20261015/w17/lights && pwd) W7_FPR_DIR=$(cd research/city_sim/w21_20261015/w17 && pwd);;
    m) C="$PY -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py scripts/CITY_w22f_assign.py"; export W20_CREEP=3 MT_BASE=actrest MT_NET=midtown_full;;
    *) C="$PY -u scripts/CITY_w9_run.py none scripts/CITY_w20_run.py scripts/CITY_w22f_assign.py";;
  esac
  W22_PROBE=$PR W22_ASSIGN=$A nice -n 5 $C "$@" --seeds $DS $SM --tag $T --out $OUT > $OUT/$T.log 2>&1 || echo "FAIL $T"' < $1; }
complete() { local bad=0; while read -r T _ _ OUT _; do grep -qs '"status": "COMPLETE"' $OUT/$T.json || { echo "INCOMPLETE $T"; bad=1; }; done < $1; return $bad; }
n4() { local P=$W20; [ $1 -lt 84 ] && P=$W19; [ "$2" = w ] && P=$A17; [ "$2" = m ] && P=$W19; echo "--n4 0.1:hyb:$P/prep/prov_rlh$1_cl.json:$P/cmodel/n2_k$1.pt"; }
same() { $PY - "$@" <<'PY'
import json, sys
a, b, days = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3].split(',')]; extra = sys.argv[4:]
F = ['timeloss', 'timeloss_agent', 'timeloss_human', 'fuel', 'fuel_agent', 'n', 'teleports', 'unfinished', 'action_digest', 'green_mean'] + extra
x = {r['seed']: r for r in json.load(open(a))['rows']}; y = {r['seed']: r for r in json.load(open(b))['rows']}
bad = [(d, f) for d in days for f in F if x[d].get(f) != y[d].get(f)]
print(('IDENTICAL ' if not bad else f'DIFFERENT {bad[:5]} ') + a.split('/')[-1] + ' vs ' + b.split('/')[-1]); sys.exit(1 if bad else 0)
PY
}
# 0. identity checks with the new wrapper
if [ "${SMOKE:-0}" != 1 ]; then J=$O/check/jobs.txt; : > $J
  for a in all none; do echo "K0_${a}_t94_s1413 $a 1 $O/check 1400,1401 g scripts/CITY_eval_n4.py $(n4 94 g) --light RL-H:94 --fleet PL:$F3/L11_s1413_fleet.pt" >> $J
    echo "KC_${a}_t94_s2213 $a 1 $O/check 1420,1421 w scripts/CITY_eval_n4.py $(n4 94 w) --light RL-H:94 --fleet PL:$F5/L11_s2213_fleet.pt" >> $J; done
  echo "K0_mix_t94_s1413 veh:0.5 1 $O/check 1400 g scripts/CITY_eval_n4.py $(n4 94 g) --light RL-H:94 --fleet PL:$F3/L11_s1413_fleet.pt" >> $J
  run_jobs $J; complete $J || { echo "checks incomplete: stop"; exit 1; }
  same $O/check/K0_all_t94_s1413.json $W20/conf/SV_t94_s1413.json 1400,1401 && same $O/check/K0_none_t94_s1413.json $W20/conf/R_t94_s1413.json 1400,1401 \
   && same $O/check/K0_mix_t94_s1413.json $B/panel/MIX_t94_s1413.json 1400 w22 \
   && same $O/check/KC_all_t94_s2213.json $A17/conf/SV_t94_s2213.json 1420,1421 && same $O/check/KC_none_t94_s2213.json $A17/conf/R_t94_s2213.json 1420,1421 \
   || { echo "KW22-0 / KW22-C FAIL with the new wrapper: stop"; exit 1; }; echo "KW22-0 and KW22-C1/C2 PASS (new wrapper)"; fi
part() { local name=$1 J=$2; shift 2; echo "W22-F $name jobs: $(wc -l < $J) $(date)"; run_jobs $J
  if complete $J; then W22_SMOKE=${SMOKE:-0} $PY scripts/CITY_w22f_report.py "$@" || echo "W22-F $name report FAIL"; echo "W22-F $name done $(date)"; else echo "W22-F $name incomplete (re-run)"; fi; }
# F1: same-day two shares
J=$O/jobs_f1.txt; : > $J
for k0 in 94 34 99 84 89; do for k in $(seq $k0 $((k0 + KR - 1))); do for s in $GS; do
  echo "S2D_t${k}_s$s vt:1800 0 $O/f1/g4 $GD g scripts/CITY_eval_n4.py $(n4 $k g) --light RL-H:$k --fleet PL:$F3/L11_s${s}_fleet.pt" >> $J; done; done; done
for k0 in 94 34 99; do for k in $(seq $k0 $((k0 + KR - 1))); do for s in $WS; do
  echo "S2D_t${k}_s$s vt:1800 0 $O/f1/w17 $WD w scripts/CITY_eval_n4.py $(n4 $k w) --light RL-H:$k --fleet PL:$F5/L11_s${s}_fleet.pt" >> $J; done; done; done
part F1 $J f1 $O/f1
# F3: probe 2, grid4 and W17, RMP and AH, SWB / all / none, 4 days
J=$O/jobs_f3.txt; : > $J
for k0 in 94 34; do for k in $(seq $k0 $((k0 + KR - 1))); do
  for s in $GS; do X="scripts/CITY_eval_n4.py $(n4 $k g) --light RL-H:$k --fleet PL:$F3/L11_s${s}_fleet.pt"
    echo "P2SWB_t${k}_s$s swb:300:0.5 2 $O/g4 $G3D g $X" >> $J; echo "P2ALL_t${k}_s$s all 2 $O/g4 $G3D g $X" >> $J; echo "P2NONE_t${k}_s$s none 2 $O/g4 $G3D g $X" >> $J; done
  for s in $WS; do X="scripts/CITY_eval_n4.py $(n4 $k w) --light RL-H:$k --fleet PL:$F5/L11_s${s}_fleet.pt"
    echo "P2SWB_t${k}_s$s swb:300:0.5 2 $O/w17 $W3D w $X" >> $J; echo "P2ALL_t${k}_s$s all 2 $O/w17 $W3D w $X" >> $J; echo "P2NONE_t${k}_s$s none 2 $O/w17 $W3D w $X" >> $J; done; done; done
part F3 $J f3 $O
# F4: Midtown area design (MT-E setting), AH and B2D, all / none / AREA / MIX, probe 3
J=$O/jobs_f4.txt; : > $J
for k0 in 34 59; do [ "${SMOKE:-0}" = 1 ] && [ $k0 != 34 ] && continue; for k in $(seq $k0 $((k0 + KR - 1))); do for s in $MS; do
  X="scripts/CITY_eval_n4.py $(n4 $k m) --light RL-H:$k --fleet PL:$F3/L11_s${s}_fleet.pt"
  echo "ALL_t${k}_s$s all 3 $O/mt $MD m $X" >> $J; echo "NONE_t${k}_s$s none 3 $O/mt $MD m $X" >> $J
  echo "AREA_t${k}_s$s area:4:2 3 $O/mt $MD m $X" >> $J; echo "MIX_t${k}_s$s veh:0.5 3 $O/mt $MD m $X" >> $J; done; done; done
part F4 $J f4 $O/mt
# F2: other W19 families, MIX p 0.3 / 0.5 / 0.7
J=$O/jobs_f2.txt; : > $J
for k0 in 39 44 49 54 59 64 69 74 79; do [ "${SMOKE:-0}" = 1 ] && [ $k0 != 49 ] && continue; for k in $(seq $k0 $((k0 + KR - 1))); do for s in $GS; do
  for p in 30 50 70; do echo "MIXp${p}_t${k}_s$s veh:0.${p%0} 0 $O/f2 $GD g scripts/CITY_eval_n4.py $(n4 $k g) --light RL-H:$k --fleet PL:$F3/L11_s${s}_fleet.pt" >> $J; done; done; done; done
part F2 $J f2 $O/f2
echo "W22-F end $(date); $(pmset -g batt | sed -n 2p | cut -c1-60)"
