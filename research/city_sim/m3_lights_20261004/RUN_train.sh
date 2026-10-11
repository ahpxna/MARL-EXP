#!/usr/bin/env bash
# M3 Amendment A1 C2: five new independent RL-H light seeds (frozen Q7b recipe, DQN seed 11 + 100 t), for the M3 confirmation only.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; D=research/city_sim/m3_lights_20261004
for t in 4 5 6 7 8; do nice -n 5 external_envs/city_runtime/bin/python -u scripts/CITY_q7b_contract.py --out $D --train-light RL-H_t$t --t $t --episodes 120 > $D/train_t$t.out 2>&1 & done
wait; echo "lights done $(date)"
