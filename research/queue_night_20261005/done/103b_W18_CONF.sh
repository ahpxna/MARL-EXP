#!/usr/bin/env bash
# W18 confirmation (PROTOCOL_CITY_WAVE18_20261008): fresh traffic peak 1360-1379 (grid4) and off-peak 1380-1399 (grid4_p4), generated after
# a non-existence check; each family's screen candidate vs its OFF x HBEFA4 / PHEMlight5; report (alpha 0.01, material = upper < -3 %).
# SMOKE=1: seed 860 (peak) / 660 (off-peak), into W18_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W18_DIR:-research/city_sim/w18_20261008}; mkdir -p $D/conf; export XPLAY_TMP=$(cd $D/check && pwd); P5=PHEMlight5/PC_EU4_G
RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; W17F=research/city_sim/w17_20261008/fresh5/fleets; echo "W18-CONF start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; CP="860"; CO="660"; else SM=""; CP="$(seq -s ' ' 1360 1379)"; CO="$(seq -s ' ' 1380 1399)"
  # fixed 21:3x (the first attempt split the seed list inside the loop header and generated only 1360 / 1380, never simulated; see C-222)
  gen() { dd=$1; per=$2; mk=$3; shift 3; GD=research/city_sim/demand/$dd; [ -f $GD/${mk}_generated ] && return 0
    for s in "$@"; do if [ -f $GD/rou_s$s.xml ]; then [ "$s" = 1360 ] || [ "$s" = 1380 ] || { echo "KW18-4 FAIL: $dd rou_s$s existed"; exit 1; }; fi; done
    for s in "$@"; do $PY $RT -n research/city_sim/net/grid4.net.xml -o $GD/trips_s$s.xml -r $GD/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period $per > /dev/null 2>&1 || { echo "GEN FAIL $dd $s"; exit 1; }; done
    date > $GD/${mk}_generated; echo "traffic $dd $mk generated $(date)"; }
  gen grid4 2.0 CONF1360 $CP; gen grid4_p4 4.0 CONF1380 $CO; fi
J=$D/conf_jobs.txt; : > $J
$PY -c "
import json; C=json.load(open('$D/screen/candidates.json')); W17F='$W17F'; D='$D'
spec=lambda a,f: {'BASE':f'PL:{W17F}/L11_{f}_fleet.pt','D4a':f'PL:{W17F}/L11_{f}_fleet.pt','D4b':f'PL:{W17F}/L11_{f}_fleet.pt','D1':f'PL:{D}/fleets/D1_{f}_fleet.pt',
  'D2a':f'PLQ:{D}/fleets/D2a_rule.pt','D2b':f'PLQ:{D}/fleets/D2b_{f}_fleet.pt','D3':f'PL:{D}/fleets/D3_{f}_fleet.pt'}.get(a) or ('GENTLE:'+{'D5g10':'1.0','D5g15':'1.5','D5g20':'2.0'}[a])
env={'OFF':'-','OFF75':'RHO=0.75','OFF100':'RHO=1.0','OFFP4':'DEM=p4'}; offs=set()
for fam,c in C.items():
    if not c: continue
    a,off=c['arm'],c['off']; e=env[off]; offs.add(off)
    for x,E in (('','-'),('P5','$P5')):
        for f in c['fleets']: print(f'{a}{x}_t0_{f} {e} {E} --light FT --fleet {spec(a,f)}')
for off in sorted(offs):
    for x,E in (('','-'),('P5','$P5')): print(f'{off}{x}_t0_h {env[off]} {E} --light FT --fleet L-ACT:0 --guard always')
" > $J || { echo "conf job list FAIL"; exit 1; }
export PY SM OUT=$D/conf CP CO
xargs -P 6 -L 1 bash -c 'T=$0; V=$1; E=$2; shift 2; [ -f $OUT/$T.json ] && exit 0; SS="$CP"
  case $V in RHO=*) export W18_RHO=${V#RHO=};; DEM=*) export W18_DEMAND=${V#DEM=}; SS="$CO";; esac; if [ "$E" != "-" ]; then export W17_EM=$E; fi
  nice -n 5 $PY -u scripts/CITY_w18_world.py scripts/CITY_w13_modes.py scripts/CITY_eval6_v11.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "confirmation failure: stop"; exit 1; }
grep -q "KW17-0 FAIL" $D/conf/run.log && { echo "KW18-0 FAIL in rows: stop"; exit 1; }
W18_SMOKE=${SMOKE:-0} $PY scripts/CITY_w18_report.py confirm $D || { echo "report FAIL"; exit 1; }
echo "W18-CONF done $(date)"
