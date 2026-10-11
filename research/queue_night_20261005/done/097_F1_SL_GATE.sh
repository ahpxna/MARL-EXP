#!/usr/bin/env bash
# F1-0 + F1-1 (PROTOCOL_CITY_F1_SALTLAKE_20261008 + A1): Salt Lake City corridors with recorded 2023 demand.  Demand and programs were
# built (CITY_sl_build demand / programs; KSL-1, KSL-3 PASS, 08/10 05:18-09:13).  This job: light training (LightRLK DQN, RL-H recipe,
# 120 episodes, seeds 11 / 12, TRAIN days in rotation) per site; FT and RL on the 10 DEV days (all SUMO cars); KSL-2 and G1 report.
# SMOKE=1: 2 episodes (300 s), first 2 TRAIN days, first 3 DEV days, into SL_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${SL_DIR:-research/city_sim/f1_saltlake/gate}; mkdir -p $D/lights; echo "F1-SL-GATE start $(date)"
DAYS() { $PY -c "import sys; sys.path.insert(0,'.'); from scripts.CITY_sl_build import days; print(' '.join(str(d.timetuple().tm_yday) for d in days('$1','$2')))"; }
for site in 400sX200w stateXuniversity; do
  TR="$(DAYS $site train)"; DV="$(DAYS $site dev)"; EP=120; SM=""
  if [ "${SMOKE:-0}" = 1 ]; then TR="$(echo $TR | cut -d' ' -f1-2)"; DV="$(echo $DV | cut -d' ' -f1-3)"; EP=2; SM="--smoke"; fi
  NET=research/city_sim/net/saltlake_$site.net.xml; ROU="research/city_sim/demand/saltlake/$site/rou_s{}.xml"
  for k in 11 12; do [ -f $D/lights/RLK_${site}_$k.pt ] || SL_SITE=$site nice -n 5 $PY -u scripts/CITY_sl_run.py scripts/CITY_sl_train_light.py --net $NET --rou "$ROU" --seed $k --episodes $EP --days $TR --name RLK_${site}_$k --out $D/lights $SM > $D/lights/train_${site}_$k.out 2>&1 & done
done; wait
for site in 400sX200w stateXuniversity; do for k in 11 12; do [ -f $D/lights/RLK_${site}_$k.pt ] || { echo "missing light $site $k: stop"; tail -3 $D/lights/train_${site}_$k.out; exit 1; }; done; done
for site in 400sX200w stateXuniversity; do
  DV="$(DAYS $site dev)"; [ "${SMOKE:-0}" = 1 ] && DV="$(echo $DV | cut -d' ' -f1-3)"
  [ -f $D/FT_$site.json ] || SL_SITE=$site nice -n 5 $PY -u scripts/CITY_sl_run.py scripts/CITY_m4s_tsi_eval.py --tk none --light FT --seeds $DV --tag FT_$site --out $D >> $D/run.log 2>&1 || { echo "FT FAIL $site"; exit 1; } &
  for k in 11 12; do [ -f $D/RLK${k}_$site.json ] || SL_SITE=$site nice -n 5 $PY -u scripts/CITY_sl_run.py scripts/CITY_m4s_tsi_eval.py --tk none --light RLK:$D/lights/RLK_${site}_$k.pt --seeds $DV --tag RLK${k}_$site --out $D >> $D/run.log 2>&1 || { echo "RL FAIL $site $k"; exit 1; } & done
done; wait
$PY scripts/CITY_sl_gate_report.py $D || { echo "report FAIL"; exit 1; }
echo "F1-SL-GATE done $(date)"
