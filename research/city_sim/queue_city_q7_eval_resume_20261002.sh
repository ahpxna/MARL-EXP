#!/usr/bin/env bash
# Q7 eval resume (02/10/2026 22:1x EDT): the 22:08 session exit killed the eval of queue_city_q7_20261002.sh after 27 of its
# runs; all four checkpoints were saved (RL-H 21:51, L-ACT 21:55, RL-J 22:02, L-RLH 22:07).  The partial eval files are archived
# to legacy/ first; the eval is re-run whole (deterministic seeds 100-104).
cd /Users/phanan/cig-amf-main; PY=external_envs/city_runtime/bin/python; D=research/city_sim/q7_cross_version_20261002
TS=$(date +%Y%m%d_%H%M%S); mkdir -p legacy/q7_eval_partial_$TS
for f in eval.log eval_rows.json tripinfo; do [ -e $D/$f ] && mv $D/$f legacy/q7_eval_partial_$TS/; done
echo "eval start $(date)"; nice -n 12 $PY -u scripts/CITY_q7_cross_version.py --out $D --eval > $D/eval.log 2>&1; tail -14 $D/eval.log
echo "Q7 end $(date)"
