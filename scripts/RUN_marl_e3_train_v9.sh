#!/usr/bin/env bash
# New trainings from 29/09 23:4x use trainer v9 with the SAMPLED leaf walk (--audit-every 5; checks 1-6 every step), approved
# by the user.  Self-check passed 23:4x (scratchpad audit_selfcheck.py): agrees with the full audit on real views at all 26
# steps; a planted object leaf is caught at sampled steps; a planted outside-final-set inbox is caught at every step.
# Identity: v9 --audit-every 5 reproduces the full-audit trainer (4 iterations: train 2569, select 3831).
# Watchdog with in-place resume.  Usage: bash scripts/RUN_marl_e3_train_v9.sh <tag>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; tag="$1"
COMMON=(--iters 2000 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --eval-every 20 --threads 2 --audit-every 5)
case "$tag" in
  rc_h256_s0)     ARGS=(--seed 0 --hidden 256 --delivery prefix);;                 # H7: flat actor, twice the width
  set_fullq4_s1)  ARGS=(--seed 1 --hidden 128 --delivery full --set-actor --quant 4);;
  *) echo "unknown $tag"; exit 2;;
esac
[ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
echo "train $tag $(date)"
"$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_train_delivery_v9.py \
  --out "$D/$tag" "${COMMON[@]}" "${ARGS[@]}"
echo "exit $? $tag $(date)"
