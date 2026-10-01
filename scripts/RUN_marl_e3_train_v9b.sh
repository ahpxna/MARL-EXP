#!/usr/bin/env bash
# Seed-1 replicate of set_fresh_s0 (29/09 23:5x; ledger L-139): set actor, prefix delivery, fresh-only inputs, scratch recipe,
# trainer v9 with the approved sampled audit (--audit-every 5; identity with the full audit checked 23:2x).
# (RUN_marl_e3_train_v9.sh is running and is not edited.)  Watchdog with in-place resume.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; tag=set_fresh_s1
[ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
echo "train $tag $(date)"
"$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_train_delivery_v9.py \
  --out "$D/$tag" --seed 1 --iters 2000 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 --eval-every 20 \
  --threads 2 --audit-every 5 --delivery prefix --arch set --adapter freshonly
echo "exit $? $tag $(date)"
