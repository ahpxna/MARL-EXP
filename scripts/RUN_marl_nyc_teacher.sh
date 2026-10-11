#!/usr/bin/env bash
# PROTOCOL_E3_NYC16X3_20261002.md: stage 1 only (the teacher), so that scripts/RUN_marl_nyc.sh (stages 2-5) is read by bash only
# after the teacher finishes and can still be corrected before then (never edit a running script).  Same command as its stage 1.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
s=$1; A=research/marl_budget/e3_nyc16x3_20261002/actors; mkdir -p "$A"; W="scripts/MARL_nyc_wrapper.py --relay-slots none --"; t=set_full_s$s
[ -f "$A/$t/manifest.json" ] && { echo "done $t"; exit 0; }
f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }
[ -e "$A/$t" ] && [ ! -f "$A/$t/state_last.pt" ] && mv "$A/$t" "legacy/nyc_${t}_nostate_$(date +%Y%m%d_%H%M%S)"
echo "train $t $(date)"
"$PY" scripts/run_with_watchdog.py --log "$A/$t.log" --stall 2400 --retries 20 -- "$PY" -u $W scripts/MARL_e3_actor_train_delivery_v6.py \
  --seed $s --iters 2000 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 --eval-every 20 --threads 2 \
  --set-actor --delivery full --out "$A/$t" || { echo "FAIL $t"; exit 1; }
[ -f "$A/$t/manifest.json" ] && echo "teacher $t done $(date)"
