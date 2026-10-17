#!/usr/bin/env bash
# W22-D (PROTOCOL_CITY_WAVE22_20261017, Amendment W22-D): alternating network switchbacks NSWa900 (burn-in 225 s) and NSWa1200 (300 s), RMP / AH /
# RWV, fleets s1413 / s1513, days 1400-1409, grid4 W20 setting; KW22-0 with the edited wrapper first; battery guard as RUN_w22abc.sh.
# SMOKE=1: RMP t94, s1413, day 1400, --smoke, into .../w22_20261017/smoke_d (checks skipped).
set -o pipefail; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W22_PROBE=1
PY=external_envs/city_runtime/bin/python; F3=research/city_sim/w15_20261007/fresh3/fleets; W19=research/city_sim/w19_20261008; W20=research/city_sim/w20_20261009; B=research/city_sim/w22_20261017
if [ "${SMOKE:-0}" = 1 ]; then O=$B/smoke_d; SM="--smoke"; FAMS="RMP:94-94:w20"; FS="1413"; DS="1400"; else O=$B/d; SM=""; FAMS="RMP:94-98:w20 AH:34-38:w19 RWV:99-103:w20"; FS="1413 1513"; DS="1400,1401,1402,1403,1404,1405,1406,1407,1408,1409"; fi
mkdir -p $O/check0 $O/tmp; export XPLAY_TMP=$(cd $O/tmp && pwd) PY SM
echo "W22-D start $(date); out $O; $(pmset -g batt | sed -n 2p | cut -c1-60)"
echo "sources: $(shasum -a 256 scripts/CITY_w22_assign.py scripts/CITY_w22d_report.py scripts/CITY_eval_n4.py scripts/CITY_w20_run.py scripts/CITY_w9_run.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
run_jobs() { xargs -P ${LANES:-6} -L 1 bash -c 'T=$0; A=$1; OUT=$2; DS=${3//,/ }; NB=$4; shift 4
  grep -qs "\"status\": \"COMPLETE\"" $OUT/$T.json && exit 0
  b=$(pmset -g batt | grep -o "[0-9]*%" | head -1 | tr -d %); pmset -g batt | grep -q "discharging" && [ "$b" -le 20 ] && { echo "SKIP $T (battery $b%)"; exit 0; }
  W22_NB=$NB W22_ASSIGN=$A nice -n 5 $PY -u scripts/CITY_w9_run.py none scripts/CITY_w20_run.py scripts/CITY_w22_assign.py "$@" --seeds $DS $SM --tag $T --out $OUT > $OUT/$T.log 2>&1 || echo "FAIL $T"' < $1; }
complete() { local bad=0; while read -r T _ OUT _; do grep -qs '"status": "COMPLETE"' $OUT/$T.json || { echo "INCOMPLETE $T"; bad=1; }; done < $1; return $bad; }
n4() { local P=$W20; [ $1 -lt 84 ] && P=$W19; echo "--n4 0.1:hyb:$P/prep/prov_rlh$1_cl.json:$P/cmodel/n2_k$1.pt"; }
same() { $PY - "$@" <<'PY'
import json, sys
a, b, days = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3].split(',')]; extra = sys.argv[4:]
F = ['timeloss', 'timeloss_agent', 'timeloss_human', 'fuel', 'fuel_agent', 'n', 'teleports', 'unfinished', 'action_digest', 'green_mean'] + extra
x = {r['seed']: r for r in json.load(open(a))['rows']}; y = {r['seed']: r for r in json.load(open(b))['rows']}
bad = [(d, f) for d in days for f in F if x[d].get(f) != y[d].get(f)]
print(('IDENTICAL ' if not bad else f'DIFFERENT {bad[:5]} ') + a.split('/')[-1] + ' vs ' + b.split('/')[-1]); sys.exit(1 if bad else 0)
PY
}
if [ "${SMOKE:-0}" != 1 ]; then J=$O/check0/jobs.txt; : > $J
  for a in all none; do echo "K0_${a}_t94_s1413 $a $O/check0 1400,1401 120 scripts/CITY_eval_n4.py $(n4 94) --light RL-H:94 --fleet PL:$F3/L11_s1413_fleet.pt" >> $J; done
  echo "K0_mix_t94_s1413 veh:0.5 $O/check0 1400 120 scripts/CITY_eval_n4.py $(n4 94) --light RL-H:94 --fleet PL:$F3/L11_s1413_fleet.pt" >> $J
  run_jobs $J; complete $J || { echo "KW22-0 rows incomplete: stop"; exit 1; }
  same $O/check0/K0_all_t94_s1413.json $W20/conf/SV_t94_s1413.json 1400,1401 && same $O/check0/K0_none_t94_s1413.json $W20/conf/R_t94_s1413.json 1400,1401 \
   && same $O/check0/K0_mix_t94_s1413.json $B/panel/MIX_t94_s1413.json 1400 w22 || { echo "KW22-0 FAIL: stop"; exit 1; }; echo "KW22-0 PASS"; fi
J=$O/jobs.txt; : > $J
for f in $FAMS; do r=${f#*:}; r=${r%%:*}; for k in $(seq ${r%-*} ${r#*-}); do for s in $FS; do X="scripts/CITY_eval_n4.py $(n4 $k) --light RL-H:$k --fleet PL:$F3/L11_s${s}_fleet.pt"
  echo "NSWa900_t${k}_s$s nswa:900 $O $DS 225 $X" >> $J; echo "NSWa1200_t${k}_s$s nswa:1200 $O $DS 300 $X" >> $J; done; done; done
echo "W22-D jobs: $(wc -l < $J)"; run_jobs $J
if complete $J; then W22_SMOKE=${SMOKE:-0} $PY scripts/CITY_w22d_report.py $O "$FAMS" "$FS" "${DS//,/ }" "NSWa900 NSWa1200" || echo "W22-D report FAIL"; echo "W22-D done $(date)"; else echo "W22-D incomplete (re-run)"; fi
