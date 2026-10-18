#!/usr/bin/env bash
# W22-F post-hoc provenance check KW22-F2 (PROTOCOL_CITY_WAVE22_20261017, after the W22-F result note): F2 took its truth (SV, R) from the W19
# rows, produced by the W19 chain (CITY_w9_run none -> CITY_w19_run -> CITY_w13_modes -> evaluator); the W22-F chain (CITY_w9_run none ->
# CITY_w20_run -> CITY_w22f_assign -> evaluator) had been checked against W19 rows only for AH (t34, KW22-1). Here: W22_ASSIGN=all / none for the
# first light of each F2 family, fleet s1413, day 1400, against the W19 SV / R rows on the row fields.  Out: research/city_sim/w22_20261017/f/check2.
set -o pipefail; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1
PY=external_envs/city_runtime/bin/python; F3=research/city_sim/w15_20261007/fresh3/fleets; W19=research/city_sim/w19_20261008; O=research/city_sim/w22_20261017/f/check2
mkdir -p $O/tmp; export XPLAY_TMP=$(cd $O/tmp && pwd)
echo "KW22-F2 start $(date); $(pmset -g batt | sed -n 2p | cut -c1-60)"
echo "sources: $(shasum -a 256 scripts/CITY_w22f_assign.py scripts/CITY_eval_n4.py scripts/CITY_w20_run.py scripts/CITY_w9_run.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
J=$O/jobs.txt; : > $J
for k in 39 44 49 54 59 64 69 74 79; do for a in all none; do
  echo "K2_${a}_t${k}_s1413 $a $k" >> $J; done; done
xargs -P ${LANES:-9} -L 1 bash -c 'T=$0; A=$1; k=$2; grep -qs "\"status\": \"COMPLETE\"" '$O'/$T.json && exit 0
  W22_PROBE=0 W22_ASSIGN=$A nice -n 5 '$PY' -u scripts/CITY_w9_run.py none scripts/CITY_w20_run.py scripts/CITY_w22f_assign.py scripts/CITY_eval_n4.py \
    --n4 0.1:hyb:'$W19'/prep/prov_rlh${k}_cl.json:'$W19'/cmodel/n2_k${k}.pt --light RL-H:$k --fleet PL:'$F3'/L11_s1413_fleet.pt \
    --seeds 1400 --tag $T --out '$O' > '$O'/$T.log 2>&1 || echo "FAIL $T"' < $J
$PY - $O $W19/conf <<'PY'
import json, sys
from pathlib import Path
O, C = Path(sys.argv[1]), Path(sys.argv[2])
F = ['timeloss', 'timeloss_agent', 'timeloss_human', 'fuel', 'fuel_agent', 'n', 'teleports', 'unfinished', 'action_digest', 'green_mean']
ok = tot = 0
for k in (39, 44, 49, 54, 59, 64, 69, 74, 79):
    for a, ref in (('all', 'SV'), ('none', 'R')):
        p = O / f'K2_{a}_t{k}_s1413.json'
        if not p.exists() or json.loads(p.read_text()).get('status') != 'COMPLETE':
            print(f'INCOMPLETE {p.name}'); tot += 1; continue
        x = {r['seed']: r for r in json.loads(p.read_text())['rows']}[1400]
        y = {r['seed']: r for r in json.loads((C / f'{ref}_t{k}_s1413.json').read_text())['rows']}[1400]
        bad = [f for f in F if x.get(f) != y.get(f)]; tot += 1; ok += not bad
        print(('IDENTICAL ' if not bad else f'DIFFERENT {bad} ') + f'{p.name} vs {ref}_t{k}_s1413 day 1400')
print(f'KW22-F2: {ok} of {tot} identical -> ' + ('PASS' if ok == tot else 'FAIL'))
PY
echo "KW22-F2 end $(date)"
