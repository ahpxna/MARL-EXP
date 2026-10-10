#!/usr/bin/env bash
# W6-4 LCD (PROTOCOL_CITY_WAVE6_20261005): train LCD j0 / j1 (120 episodes, SUMO cars) -> DEV gate on 600-611 (LCD alone vs RL-H k0 / k1, city TL
# upper < +0.5, light seeds unpaired) -> if PASS: confirmation on 760-779 (LCDF vs R; LCD alone vs RL-H alone; KN8-1) -> report.  SMOKE=1: tiny.
set -eo pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W6_DIR:-research/city_sim/w6_20261005/lcd}; mkdir -p $D/check $D/train $D/dev $D/conf; export XPLAY_TMP=$(cd "$D/check" && pwd)
G=research/city_sim/demand/grid4; P=research/city_sim/spat_pilot_20261004/fleets_v11; RUN="$PY -u scripts/CITY_f1a1_run.py"; echo "W6-LCD start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; EP=2; DS="600"; CS="600"; FLS="s213"; LTS="4"; else SM=""; EP=120; DS="$(seq -s ' ' 600 611)"; CS="$(seq -s ' ' 760 779)"; FLS="s213 s313 s413 s513"; LTS="4 5 6 7 8"
  [ -f $G/CONF760_generated ] || { echo "traffic 760-779 not generated (job 051): stop"; exit 1; }; fi
export PY D RUN SM
for j in 0 1; do [ -f $D/train/LCD_j$j.pt ] || nice -n 5 $PY -u scripts/CITY_lcd.py --seed $j --episodes $EP $SM --out $D/train > $D/train/LCD_j$j.out 2>&1 & done; wait
for j in 0 1; do [ -f $D/train/LCD_j$j.pt ] || { echo "missing LCD_j$j: stop"; exit 1; }; done; echo "training done $(date)"
J=$D/dev_jobs.txt; : > $J
for j in 0 1; do echo "LCDA_dev_j$j scripts/CITY_eval_n9.py --spat none --light LCD:$D/train/LCD_j$j.pt --fleet human" >> $J; done
for k in 0 1; do echo "RLHA_dev_k$k scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$k --fleet human" >> $J; done
export SS="$DS"; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/dev/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/dev >> $D/dev/run.log 2>&1 || { echo "FAIL $T"; exit 1; }' < $J
$PY - <<PYC || { echo "GATE computation FAIL"; exit 1; }
import json, sys; sys.path.insert(0, '.')
import scripts.CITY_w6_report_v2 as W; from scripts.CITY_w6_validation import rows
Rt = rows('$D/dev'); S = [int(s) for s in '$DS'.split()]
r = W.unpaired(Rt, lambda l, f: f'LCDA_dev_j{l}', (0, 1), lambda l, f: f'RLHA_dev_k{l}', (0, 1), ('x',), S, metrics=('timeloss',))
g = dict(city_tl=r['timeloss'], agent_none=True, pass_=bool(r['timeloss']['up'] < 0.5), durs={j: json.load(open(f'$D/dev/LCDA_dev_j{j}_n8.json'))['dur_mean'] for j in (0, 1)})
g['pass'] = g.pop('pass_'); open('$D/gate.json', 'w').write(json.dumps(g, indent=1)); print('DEV gate', json.dumps(g))
PYC
[ "${SMOKE:-0}" = 1 ] && [ "${FORCE_GATE:-0}" = 1 ] && $PY -c "import json; g = json.load(open('$D/gate.json')); g['pass'] = True; g['forced_in_smoke'] = True; json.dump(g, open('$D/gate.json', 'w'))"   # smoke only: exercise the confirmation branch
if $PY -c "import json,sys; sys.exit(0 if json.load(open('$D/gate.json'))['pass'] else 1)"; then
  J=$D/conf_jobs.txt; : > $J
  for j in 0 1; do echo "LCDA_j$j scripts/CITY_eval_n9.py --spat none --light LCD:$D/train/LCD_j$j.pt --fleet human" >> $J
    for fl in $FLS; do echo "LCDF_j${j}_$fl scripts/CITY_eval_n9.py --spat program --light LCD:$D/train/LCD_j$j.pt --fleet PL:$P/L11_${fl}_fleet.pt" >> $J; done; done
  for t in $LTS; do echo "RLHA_t$t scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$t --fleet human" >> $J
    for fl in $FLS; do echo "R_t${t}_$fl scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$t --fleet PL:$P/L11_${fl}_fleet.pt" >> $J; done; done
  export SS="$CS"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $RUN "$@" --seeds $SS $SM --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 1; }' < $J
  $PY -c "
import json, glob
m = [json.load(open(f)) for f in glob.glob('$D/conf/LCDF_*_n8.json')]; assert m and all(x['checked'] > 0 and x['mism'] == 0 for x in m), 'KN8-1 failed'; print('KN8-1 on the panel: checked', sum(x['checked'] for x in m), 'mismatches', sum(x['mism'] for x in m))"
fi
echo "panel done $(date)"
if [ "${SMOKE:-0}" = 1 ]; then W6_SMOKE=$(dirname $D) W6_SMOKE_SEED=600 $PY scripts/CITY_w6_report_v2.py lcd; else $PY scripts/CITY_w6_report_v2.py lcd; fi; echo "W6-LCD done $(date)"
