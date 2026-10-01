#!/usr/bin/env bash
# Distillation runs after L-129 (29/09 22:5x), one tag per call, under the stall watchdog.  distill v2's default reproduces v1
# exactly (it 1-2: loss 1.973 / 1.665, agree 0.300 / 0.465).  v1 has no resume: on a stall the watchdog moves the partial
# --out to legacy/ and restarts it.
# Usage: bash scripts/RUN_marl_e3_distill_v2.sh distill_fo_prefix_s0 | distill_none_s1
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929
case "$1" in
  distill_fo_prefix_s0) ARGS=(--teacher "$D/set_full_s0/ckpt_best.pt" --student-delivery prefix --student-adapter freshonly --seed 0);;
  distill_none_s1)      ARGS=(--teacher "$D/set_full_s1/ckpt_best.pt" --student-delivery none --seed 1);;
  *) echo "unknown $1"; exit 2;;
esac
[ -f "$D/$1/manifest.json" ] && { echo "done $1"; exit 0; }
echo "distill $1 $(date)"
"$PY" scripts/run_with_watchdog.py --log "$D/$1.log" --out "$D/$1" --stall 900 --retries 3 -- \
  "$PY" -u scripts/MARL_e3_actor_distill_v2.py "${ARGS[@]}" --out "$D/$1" --iters 500
echo "exit $? $1 $(date)"
