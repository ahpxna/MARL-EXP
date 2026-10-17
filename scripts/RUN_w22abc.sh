#!/usr/bin/env bash
# W22-A / W22-B / W22-C (PROTOCOL_CITY_WAVE22_20261017, amendments of 17/10 02:0x).  Order C -> A -> B; a battery guard skips new jobs while
# discharging at <= 20 % (re-run to resume; a report runs only on a complete step).
#   0. KW22-0: the edited wrapper (nsw kind) reproduces SV / R (t94 s1413, days 1400-1401) and W22's MIX row (t94 s1413, day 1400)
#   C. W17 world: KW22-C1 / C2 (all / none = W21-A SV / R, t94 s2213, days 1420-1421), KW17-0 lines, SWB / MIX panel -> CITY_w22_report.py
#   A. grid4 days 1410-1419: SWB p 0.5 / 0.8 / 0.95, RMP SRL RDQ AH RWV -> CITY_w22a_report.py
#   B. grid4 days 1400-1409: MIX p 0.1 / 0.3 / 0.7 / 0.9 and NSW 600 s, RMP AH RWV -> CITY_w22b_report.py
# SMOKE=1: one cell per step, one day, --smoke, checks skipped, reports with W22_SMOKE=1, into .../w22_20261017/smoke_abc.
set -o pipefail; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W22_PROBE=1
PY=external_envs/city_runtime/bin/python; F3=research/city_sim/w15_20261007/fresh3/fleets; F5=research/city_sim/w17_20261008/fresh5/fleets
W19=research/city_sim/w19_20261008; W20=research/city_sim/w20_20261009; A17=research/city_sim/w21_20261015/w17; B=research/city_sim/w22_20261017
if [ "${SMOKE:-0}" = 1 ]; then O=$B/smoke_abc; SM="--smoke"; else O=$B; SM=""; fi
mkdir -p $O/check0 $O/w17 $O/w17/check $O/a $O/b $O/tmp; export XPLAY_TMP=$(cd $O/tmp && pwd)
echo "W22-ABC start $(date); out $O; $(pmset -g batt | sed -n 2p | cut -c1-60)"
echo "sources: $(shasum -a 256 scripts/CITY_w22_assign.py scripts/CITY_w22_report.py scripts/CITY_w22a_report.py scripts/CITY_w22b_report.py scripts/CITY_eval_n4.py scripts/CITY_w20_run.py scripts/CITY_w9_run.py scripts/CITY_w13_modes.py scripts/CITY_w17_world.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
export PY SM
# job line: <tag> <assign> <out dir> <days...|> <chain prefix id> <evaluator> <args>;  chain g = grid4 W20, w = W17 world
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
a, b, days = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3].split(',')]; extra = sys.argv[4:] if len(sys.argv) > 4 else []
F = ['timeloss', 'timeloss_agent', 'timeloss_human', 'fuel', 'fuel_agent', 'n', 'teleports', 'unfinished', 'action_digest', 'green_mean'] + extra
x = {r['seed']: r for r in json.load(open(a))['rows']}; y = {r['seed']: r for r in json.load(open(b))['rows']}
bad = [(d, f) for d in days for f in F if x[d].get(f) != y[d].get(f)]
print(('IDENTICAL ' if not bad else f'DIFFERENT {bad[:5]} ') + a.split('/')[-1] + ' vs ' + b.split('/')[-1]); sys.exit(1 if bad else 0)
PY
}
# 0. KW22-0 (edited wrapper)
if [ "${SMOKE:-0}" != 1 ]; then J=$O/check0/jobs.txt; : > $J
  for a in all none; do echo "K0_${a}_t94_s1413 $a $O/check0 1400,1401 g scripts/CITY_eval_n4.py $(n4 94 g) --light RL-H:94 --fleet PL:$F3/L11_s1413_fleet.pt" >> $J; done
  echo "K0_mix_t94_s1413 veh:0.5 $O/check0 1400 g scripts/CITY_eval_n4.py $(n4 94 g) --light RL-H:94 --fleet PL:$F3/L11_s1413_fleet.pt" >> $J
  run_jobs $J; complete $J || { echo "KW22-0 rows incomplete: stop"; exit 1; }
  same $O/check0/K0_all_t94_s1413.json $W20/conf/SV_t94_s1413.json 1400,1401 && same $O/check0/K0_none_t94_s1413.json $W20/conf/R_t94_s1413.json 1400,1401 \
   && same $O/check0/K0_mix_t94_s1413.json $B/panel/MIX_t94_s1413.json 1400 w22 || { echo "KW22-0 FAIL: stop"; exit 1; }; echo "KW22-0 PASS"; fi
# C. W17 world
if [ "${SMOKE:-0}" = 1 ]; then CF="RMP:94-94"; CS="2213"; CD="1420"; else CF="RMP:94-98 AH:34-38 RWV:99-103"; CS="2213 2313"; CD="1420,1421,1422,1423,1424,1425,1426,1427,1428,1429"; fi
if [ "${SMOKE:-0}" != 1 ]; then J=$O/w17/check/jobs.txt; : > $J
  for a in all none; do echo "KC_${a}_t94_s2213 $a $O/w17/check 1420,1421 w scripts/CITY_eval_n4.py $(n4 94 w) --light RL-H:94 --fleet PL:$F5/L11_s2213_fleet.pt" >> $J; done
  run_jobs $J; complete $J || { echo "KW22-C rows incomplete: stop"; exit 1; }
  same $O/w17/check/KC_all_t94_s2213.json $A17/conf/SV_t94_s2213.json 1420,1421 && same $O/w17/check/KC_none_t94_s2213.json $A17/conf/R_t94_s2213.json 1420,1421 \
   || { echo "KW22-C1/C2 FAIL: stop"; exit 1; }; echo "KW22-C1/C2 PASS"; fi
J=$O/w17/jobs.txt; : > $J
for f in $CF; do r=${f#*:}; for k in $(seq ${r%-*} ${r#*-}); do for s in $CS; do X="$(n4 $k w) --light RL-H:$k --fleet PL:$F5/L11_s${s}_fleet.pt"
  echo "SWB_t${k}_s$s swb:300:0.5 $O/w17 $CD w scripts/CITY_eval_n4.py $X" >> $J; echo "MIX_t${k}_s$s veh:0.5 $O/w17 $CD w scripts/CITY_eval_n4.py $X" >> $J; done; done; done
echo "W22-C jobs: $(wc -l < $J)"; run_jobs $J
if complete $J; then n=$(cat $O/w17/*.log | grep -o "KW17-0: type v_passenger tau" | wc -l); echo "KW17-0 lines: $n (jobs $(wc -l < $J))"
  grep -qs "KW17-0 FAIL" $O/w17/*.log && echo "KW17-0 FAIL" || { [ $n -ge $(wc -l < $J) ] && W22_SMOKE=${SMOKE:-0} $PY scripts/CITY_w22_report.py $O/w17 "$(for f in $CF; do echo -n "$f:$A17/conf "; done)" "$CS" "${CD//,/ }" || echo "W22-C report FAIL"; }
  echo "W22-C done $(date)"; else echo "W22-C incomplete (re-run)"; fi
# A. size-based decision, grid4 days 1410-1419
if [ "${SMOKE:-0}" = 1 ]; then AF="RMP:94-94:w20"; AS="1413"; AD="1410"; AP="50 95"; else AF="RMP:94-98:w20 SRL:84-88:w20 RDQ:89-93:w20 AH:34-38:w19 RWV:99-103:w20"; AS="1413 1513"; AD="1410,1411,1412,1413,1414,1415,1416,1417,1418,1419"; AP="50 80 95"; fi
J=$O/a/jobs.txt; : > $J
for f in $AF; do r=${f#*:}; r=${r%%:*}; for k in $(seq ${r%-*} ${r#*-}); do for s in $AS; do for p in $AP; do
  echo "SWBp${p}_t${k}_s$s swb:300:0.$( [ $p = 95 ] && echo 95 || echo ${p%0} ) $O/a $AD g scripts/CITY_eval_n4.py $(n4 $k g) --light RL-H:$k --fleet PL:$F3/L11_s${s}_fleet.pt" >> $J; done; done; done; done
echo "W22-A jobs: $(wc -l < $J)"; run_jobs $J
if complete $J; then W22_SMOKE=${SMOKE:-0} $PY scripts/CITY_w22a_report.py $O/a "$AF" "$AS" "${AD//,/ }" "$AP" || echo "W22-A report FAIL"; echo "W22-A done $(date)"; else echo "W22-A incomplete (re-run)"; fi
# B. treated-share sweep and NSW, grid4 days 1400-1409
if [ "${SMOKE:-0}" = 1 ]; then BF="RMP:94-94:w20"; BS="1413"; BD="1400"; BP="10"; else BF="RMP:94-98:w20 AH:34-38:w19 RWV:99-103:w20"; BS="1413 1513"; BD="1400,1401,1402,1403,1404,1405,1406,1407,1408,1409"; BP="10 30 70 90"; fi
J=$O/b/jobs.txt; : > $J
for f in $BF; do r=${f#*:}; r=${r%%:*}; for k in $(seq ${r%-*} ${r#*-}); do for s in $BS; do X="$(n4 $k g) --light RL-H:$k --fleet PL:$F3/L11_s${s}_fleet.pt"
  for p in $BP; do echo "MIXp${p}_t${k}_s$s veh:0.${p%0} $O/b $BD g scripts/CITY_eval_n4.py $X" >> $J; done
  echo "NSW_t${k}_s$s nsw:600:0.5 $O/b $BD g scripts/CITY_eval_n4.py $X" >> $J; done; done; done
echo "W22-B jobs: $(wc -l < $J)"; run_jobs $J
if complete $J; then W22_SMOKE=${SMOKE:-0} $PY scripts/CITY_w22b_report.py $O/b $B/$( [ "${SMOKE:-0}" = 1 ] && echo smoke || echo panel ) "$BF" "$BS" "${BD//,/ }" "$BP" || echo "W22-B report FAIL"; echo "W22-B done $(date)"; else echo "W22-B incomplete (re-run)"; fi
echo "W22-ABC end $(date); $(pmset -g batt | sed -n 2p | cut -c1-60)"
