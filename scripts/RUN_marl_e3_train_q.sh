#!/usr/bin/env bash
# Trained compressed-payload actor for the byte-budget variant (29/09 23:0x; ledger L-133): set actor, FULL delivery
# (every receiver decodes all 8 under 3 B packets and byte capacity 25 K_i, so full == the variant in training), payloads
# quantised with the TRAIN codebook, L = 4.  Trainer v8 identity passed: without --quant it reproduces set_full_s0
# (it 1-2: 2979 / 2704).  Watchdog with in-place resume (no --out).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; tag="$1"
case "$tag" in
  set_fullq4_s0) SEED=0;; set_fullq4_s1) SEED=1;; *) echo "unknown $tag"; exit 2;;
esac
[ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
echo "train $tag $(date)"
"$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_train_delivery_v8.py \
  --out "$D/$tag" --seed "$SEED" --iters 2000 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 \
  --eval-every 20 --threads 2 --delivery full --set-actor --quant 4
echo "exit $? $tag $(date)"
