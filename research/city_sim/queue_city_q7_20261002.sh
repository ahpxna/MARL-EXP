#!/usr/bin/env bash
# City queue Q7 (02/10/2026 21:4x; PROTOCOL_CITY_Q7_CROSS_VERSION_20261002.md): phase 1 RL-H ∥ L-ACT; phase 2 RL-J ∥ L-RLH; eval.
cd /Users/phanan/cig-amf-main; PY=external_envs/city_runtime/bin/python; D=research/city_sim/q7_cross_version_20261002; mkdir -p $D
echo "phase 1 start $(date)"
nice -n 12 $PY -u scripts/CITY_q7_cross_version.py --out $D --episodes 120 --train-light RL-H > $D/train_RL-H.log 2>&1 & p1=$!
nice -n 12 $PY -u scripts/CITY_q7_cross_version.py --out $D --episodes 120 --train-fleet L-ACT --against ACT > $D/train_L-ACT.log 2>&1 & p2=$!
wait $p1; wait $p2; tail -1 $D/train_RL-H.log; tail -1 $D/train_L-ACT.log
[ -f $D/RL-H.pt ] && [ -f $D/L-ACT.pt ] || { echo "phase 1 checkpoint missing: stop"; exit 1; }
echo "phase 2 start $(date)"
nice -n 12 $PY -u scripts/CITY_q7_cross_version.py --out $D --episodes 120 --train-light RL-J --with-fleet $D/L-ACT.pt > $D/train_RL-J.log 2>&1 & p3=$!
nice -n 12 $PY -u scripts/CITY_q7_cross_version.py --out $D --episodes 120 --train-fleet L-RLH --against $D/RL-H.pt > $D/train_L-RLH.log 2>&1 & p4=$!
wait $p3; wait $p4; tail -1 $D/train_RL-J.log; tail -1 $D/train_L-RLH.log
[ -f $D/RL-J.pt ] && [ -f $D/L-RLH.pt ] || { echo "phase 2 checkpoint missing: stop"; exit 1; }
echo "eval start $(date)"; nice -n 12 $PY -u scripts/CITY_q7_cross_version.py --out $D --eval > $D/eval.log 2>&1; tail -12 $D/eval.log
echo "Q7 end $(date)"
