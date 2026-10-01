#!/usr/bin/env bash
# Seeds 5-9 for BYTEBUDGET (30/09 10:5x; ledger L-161; user: "run seeds 5-9 for BYTEBUDGET").  Per seed N:
#   set_full_sN      teacher: set actor, full delivery, raw payloads (trainer v9, sampled audit)
#   distill_none_sN  0-byte student distilled from set_full_sN (distill v3 defaults = the v1 recipe)
#   set_none_sN      same-architecture no-communication reference
# Watchdog on every run.  Usage: <tag> [<tag> ...]  (run in order; a tag already COMPLETE is skipped)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929
COMMON=(--iters 2000 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 --eval-every 20 --threads 2 --audit-every 5)
for tag in "$@"; do
  [ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  N="${tag##*_s}"
  case "$N" in 5|6|7|8|9) ;; *) echo "bad seed in $tag"; exit 2;; esac
  echo "run $tag $(date)"
  case "$tag" in
    set_full_s*) "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_train_delivery_v9.py \
                   --out "$D/$tag" "${COMMON[@]}" --seed "$N" --delivery full --set-actor;;
    set_none_s*) "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_train_delivery_v9.py \
                   --out "$D/$tag" "${COMMON[@]}" --seed "$N" --delivery none --set-actor;;
    distill_none_s*) "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill_v3.py \
                   --teacher "$D/set_full_s$N/ckpt_best.pt" --student-delivery none --seed "$N" --out "$D/$tag" --iters 500;;
    *) echo "unknown $tag"; exit 2;;
  esac
  echo "exit $? $tag $(date)"
done
