#!/usr/bin/env bash
# M4 stage 4b (Amendment M4-A7): runs ONLY if f1a1_20261004/report_f1a1.txt says CONFIRMED.  KK-1 (done, s4b/check) -> KK-4 traffic 1020-1039
# -> 4 F1k trainings (200 episodes) -> KK-2 / KK-3 -> 12 eval jobs -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; SP=research/city_sim/m4_20261004/spider; D=$SP/s4b
grep -q "F1-A1 GATE -> CONFIRMED" research/city_sim/f1a1_20261004/report_f1a1.txt || { echo "F1-A1 not confirmed: 4b not run (registered)"; exit 0; }
grep -q "FORECAST-K CONVENTION: PASS" $D/check/kk1_conv.txt && grep -q "FORECAST-K CONVENTION: FAIL" $D/check/kk1_negative_control.txt || { echo "KK-1 FAIL"; exit 1; }
G=research/city_sim/demand/spider/p2.0; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; RULE=research/city_sim/f1_20261004/train/RULE0_fleet.pt
mkdir -p $D/train $D/eval/tmp
if [ ! -f $D/check/traffic_generated ]; then
  for s in $(seq 1020 1039); do [ -f $G/rou_s$s.xml ] && { echo "KK-4 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 1020 1039); do $PY $RT -n research/city_sim/net/spider.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger \
    --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; echo "KK-4 PASS $(date)" | tee $D/check/traffic_generated; fi
for p in "213 11" "313 11" "413 111" "513 111"; do set -- $p; nice -n 5 $PY -u scripts/CITY_fleet_train_f1k.py --seed $1 --light-ckpt $SP/RLK_sp$2.pt --init scratch \
  --table $D/prov/fk_rlk$2.json --q 0.1 --episodes 200 --name F1k_s$1 --out $D/train > $D/train/F1k_s$1.out 2>&1 & done; wait; echo "training done $(date)"
$PY - <<PYC || { echo "KK-2 FAIL"; exit 1; }
import hashlib, torch
for f, k in ((213, 11), (313, 11), (413, 111), (513, 111)):
    d = torch.load('$D/train/F1k_s%d_fleet.pt' % f, weights_only=False); h = hashlib.sha256(open('$SP/RLK_sp%d.pt' % k, 'rb').read()).hexdigest()
    assert d['light_sha256'] == h, (f, k); print('KK-2', f, k, 'light sha ok')
PYC
S="$(seq -s ' ' 1020 1039)"; E=$D/eval; export XPLAY_TMP=$PWD/$E/tmp
ev() { nice -n 5 $PY -u scripts/CITY_m4s_f1k_eval.py "$@" --out $E >> $E/run.log 2>&1 || echo "FAIL $*"; }
for k in 11 111; do L=RLK:$SP/RLK_sp$k.pt; T=$D/prov/fk_rlk$k.json
  ev --spat-arm none --light $L --fleet GLOSAL:0.3 --seeds $S --tag R_$k & ev --spat-arm fck:0.1:$T --light $L --fleet PL:$RULE --seeds $S --tag RULE_$k &
  for f in 213 313 413 513; do ev --spat-arm fck:0.1:$T --light $L --fleet PL:$D/train/F1k_s${f}_fleet.pt --seeds $S --tag F1k_s${f}_on_$k & done; done; wait
$PY scripts/CITY_m4_s4b_report.py; echo "M4 4b done $(date)"
