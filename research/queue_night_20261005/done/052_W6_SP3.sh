#!/usr/bin/env bash
# W6-6 SPIDER-3 (PROTOCOL_CITY_WAVE6_20261005; third and last spider attempt): traffic 1150-1169 -> KS3-1 smoke -> tuning (16 jobs x TUNE 1100-1103)
# -> choice -> confirmation (8 jobs x 20 seeds) -> KS3-1 on the panel -> report (alpha 0.0125 one-sided).
set -eo pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/w6_20261005/sp3; mkdir -p $D/check $D/tune $D/conf; export XPLAY_TMP=$(cd "$D/check" && pwd)
SP=research/city_sim/m4_20261004/spider; G=research/city_sim/demand/spider/p2.0; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py
EV="$PY -u scripts/CITY_m4s_tsi_eval.py"; EV3="$PY -u scripts/CITY_m4s_tsi3_eval.py"; echo "W6-SP3 start $(date)"
if [ ! -f $G/CONF1150_generated ]; then for s in $(seq 1150 1169); do [ -f $G/rou_s$s.xml ] && { echo "KS-0 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 1150 1169); do $PY $RT -n research/city_sim/net/spider.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; date > $G/CONF1150_generated; fi
echo "spider traffic 1150-1169 ready $(date)"
[ -f $D/check/K3.json ] || $EV3 --tk3 fkd:$SP/s3b/prov/fkcl_rlk11.json --light RLKQ:$SP/RLK_sp11.pt:1:1 --fleet GLOSAL:0.3 --seeds 1100 --smoke --tag K3 --out $D/check >> $D/check/run.log 2>&1
$PY - <<PYC || { echo "KS3-1 FAIL: stop"; exit 1; }
import json, sys
p = json.load(open('$D/check/K3_tk.json'))['provider']; ok = p['valid'] > 0 and p['exc'] == 0 and p['valid'] == p['fk_direct'] + p['always']
c = json.load(open('$D/check/K3_tk.json'))['realized_checks']; ok = ok and sum(x['checked'] for x in c) > 0 and sum(x['mismatches'] for x in c) == 0
t = f'KS3-1 direct-only provider (smoke): {p}\nKS3-1: {"PASS" if ok else "FAIL"}\n'; open('$D/check/ks3_1.txt', 'w').write(t); print(t); sys.exit(0 if ok else 1)
PYC
J=$D/tune_jobs.txt; : > $J
for k in 11 111; do TB=$SP/s3b/prov/fkcl_rlk$k.json; echo "R_$k $EV --tk none --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J
  for ab in "0 0" "1 0.5" "2 0.5" "1 0.75" "2 0.75" "1 1" "2 1"; do set -- $ab; T=$(echo "T_${k}_a$1_b$2" | tr '.' 'p')
    echo "$T $EV3 --tk3 fkd:$TB --light RLKQ:$SP/RLK_sp$k.pt:$1:$2 --fleet GLOSAL:0.3" >> $J; done; done
export PY D; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/tune/$T.json ] || nice -n 5 "$@" --seeds 1100 1101 1102 1103 --tag $T --out $D/tune >> $D/tune/run.log 2>&1 || { echo "FAIL $T"; exit 1; }' < $J
$PY scripts/CITY_w6_sp3_tune.py | tee $D/tune/tune.txt || { echo "TUNE FAIL"; exit 1; }
J=$D/conf_jobs.txt; : > $J
for k in 11 111; do AB=$($PY -c "import json;print(json.load(open('$D/tune/choice.json'))['$k']['choice'].replace(',',':'))"); TB=$SP/s3b/prov/fkcl_rlk$k.json
  echo "R_$k $EV --tk none --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J; echo "TSIK3_$k $EV3 --tk3 fkd:$TB --light RLKQ:$SP/RLK_sp$k.pt:$AB --fleet GLOSAL:0.3" >> $J
  echo "SVC3_$k $EV3 --tk3 fkd:$TB --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J; echo "ADPK3_$k $EV --tk none --light RLKQ:$SP/RLK_sp$k.pt:$AB --fleet GLOSAL:0.3" >> $J; done
export SS="$(seq -s ' ' 1150 1169)"; xargs -P 6 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 "$@" --seeds $SS --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || { echo "FAIL $T"; exit 1; }' < $J
$PY - <<PYC
import json, glob
for f in sorted(glob.glob('$D/conf/TSIK3_*_tk.json')) + sorted(glob.glob('$D/conf/SVC3_*_tk.json')):
    d = json.load(open(f)); p = d['provider']; c = d['realized_checks']; assert p['exc'] == 0 and p['valid'] > 0 and sum(x['checked'] for x in c) > 0 and not sum(x['mismatches'] for x in c), f; print('KS3-1 panel', f.split('/')[-1], p, 'PASS' if p['exc'] == 0 and p['valid'] > 0 else 'FAIL')
PYC
echo "panel done $(date)"; $PY scripts/CITY_w6_report_v2.py sp3; echo "W6-SP3 done $(date)"
