#!/usr/bin/env bash
# More TRAINING SEEDS (30/09 00:5x; ledger L-148), because the seed-to-seed spread is about 7 % (set_fresh s0 vs s1) and every
# pre-registered verdict so far rests on 2 seeds.  Same recipes as seeds 0-1; trainer v9 with the approved sampled audit
# (identity with the full audit checked 23:2x).  Watchdog with in-place resume.  Usage: <tag>
#  set_full_s2   teacher seed 2: for the byte-budget variant (eval-only) and for a seed-2 0-byte student
#  set_none_s2   the same-architecture no-communication reference, seed 2
#  set_fresh_s2, set_fresh_s3   adjudicate SETFRESH's seed dependence (s0 PASS, s1 FAIL)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; tag="$1"
COMMON=(--iters 2000 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 --eval-every 20 --threads 2 --audit-every 5)
case "$tag" in
  set_full_s2)  ARGS=(--seed 2 --delivery full --set-actor);;
  set_none_s2)  ARGS=(--seed 2 --delivery none --set-actor);;
  set_fresh_s2) ARGS=(--seed 2 --delivery prefix --arch set --adapter freshonly);;
  set_fresh_s3) ARGS=(--seed 3 --delivery prefix --arch set --adapter freshonly);;
  *) echo "unknown $tag"; exit 2;;
esac
[ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
echo "train $tag $(date)"
"$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_train_delivery_v9.py \
  --out "$D/$tag" "${COMMON[@]}" "${ARGS[@]}"
echo "exit $? $tag $(date)"
