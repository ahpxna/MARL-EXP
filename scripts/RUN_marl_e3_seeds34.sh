#!/usr/bin/env bash
# Seeds 3-4 for the key lines, plus seed 2 of the trained compressed actor and of control C1 (30/09 09:0x; ledger L-154).
# Trainer v9 (sampled audit), distill v3 (defaults = the v1 recipe).  Watchdog on every run.  Usage: <tag>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; tag="$1"
COMMON=(--iters 2000 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 --eval-every 20 --threads 2 --audit-every 5)
[ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
echo "run $tag $(date)"
train() { "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_train_delivery_v9.py --out "$D/$tag" "${COMMON[@]}" "$@"; }
distill() { "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill_v3.py --out "$D/$tag" --iters 500 "$@"; }
case "$tag" in
  set_full_s3)   train --seed 3 --delivery full --set-actor;;
  set_full_s4)   train --seed 4 --delivery full --set-actor;;
  set_none_s3)   train --seed 3 --delivery none --set-actor;;
  set_none_s4)   train --seed 4 --delivery none --set-actor;;
  set_fullq4_s2) train --seed 2 --delivery full --set-actor --quant 4;;
  distill_none_s3) distill --teacher "$D/set_full_s3/ckpt_best.pt" --student-delivery none --seed 3;;
  distill_none_s4) distill --teacher "$D/set_full_s4/ckpt_best.pt" --student-delivery none --seed 4;;
  distill_none_fromnone_s2) distill --teacher "$D/set_none_s2/ckpt_best.pt" --teacher-view own --student-delivery none --seed 2;;
  *) echo "unknown $tag"; exit 2;;
esac
echo "exit $? $tag $(date)"
