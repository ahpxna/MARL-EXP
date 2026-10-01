#!/usr/bin/env bash
# Trainings for PROTOCOL_E3_FRESHONLY_20260929.md (29/09 22:3x): one tag per call, under the stall watchdog with in-place resume
# (no --out, as the resume trainer requires).  Identity checks passed 22:2x: v6 --set-actor --delivery full seed 0 reproduces
# set_full_s0 (it 1 train 2978.875); v7 --arch set --adapter freshonly --delivery prefix runs and records arch/adapter.
# Usage: bash scripts/RUN_marl_e3_train_fo.sh set_full_s1 | set_fresh_s0
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929
COMMON=(--iters 2000 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 --eval-every 20 --threads 2)
case "$1" in
  set_full_s1)  ARGS=(scripts/MARL_e3_actor_train_delivery_v6.py --out "$D/set_full_s1" --seed 1 "${COMMON[@]}" --delivery full --set-actor);;
  set_fresh_s0) ARGS=(scripts/MARL_e3_actor_train_delivery_v7.py --out "$D/set_fresh_s0" --seed 0 "${COMMON[@]}" --delivery prefix --arch set --adapter freshonly);;
  *) echo "unknown $1"; exit 2;;
esac
[ -f "$D/$1/manifest.json" ] && { echo "done $1"; exit 0; }
echo "train $1 $(date)"
"$PY" scripts/run_with_watchdog.py --log "$D/$1.log" --stall 900 --retries 3 -- "$PY" -u "${ARGS[@]}"
echo "exit $? $1 $(date)"
