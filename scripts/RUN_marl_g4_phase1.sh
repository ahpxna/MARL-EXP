#!/usr/bin/env bash
# 4x4 GRID, phase 1 (30/09 20:4x EDT; ledger L-186; user 20:0x "expand the map, no more 3x3"): for one seed, the full-information
# set teacher and the co-trained silent set actor (in parallel), then the zero-byte student, then their development-panel
# evaluations.  Same commands as the 3x3 runs (L-147 ... L-160), through scripts/MARL_grid_wrapper.py --rows 4 --cols 4
# (the 3x3 scripts are not edited).  Smoke-tested 20:3x (2 iterations each).  Watchdog on every run.
# Usage: bash scripts/RUN_marl_g4_phase1.sh <seed>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
s=$1; G=research/marl_budget/e3_grid4x4_20260930; A=$G/actors; E=$G/eval; mkdir -p "$A" "$E"
W="scripts/MARL_grid_wrapper.py --rows 4 --cols 4 --"
run() {  # tag script args...
  local tag=$1; shift
  [ -f "$A/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$A/$tag" ] && mv "$A/$tag" "legacy/g4_${tag}_partial_$(date +%Y%m%d_%H%M%S)"
  echo "train $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$A/$tag.log" --out "$A/$tag" --stall 1200 --retries 3 -- "$PY" -u $W "$@" --out "$A/$tag" || echo "FAIL $tag"
}
ev() {  # tag actor deliveries
  local tag=$1 actor=$2 dels=$3
  [ -f "$A/$actor/manifest.json" ] || { echo "skip $tag"; return 0; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 600 --retries 3 -- "$PY" -u $W scripts/MARL_e3_delivery_eval_v6.py \
    --actors "$actor=$A/$actor/ckpt_best.pt" --deliveries $dels --capacity iid --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
TR="--seed $s --iters 2000 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 --eval-every 20 --threads 2 --set-actor"
run set_full_s$s scripts/MARL_e3_actor_train_delivery_v6.py $TR --delivery full &
run set_none_s$s scripts/MARL_e3_actor_train_delivery_v5.py $TR --delivery none &
wait
run distill_none_s$s scripts/MARL_e3_actor_distill.py --teacher "$A/set_full_s$s/ckpt_best.pt" --student-delivery none --seed $s --iters 500 --threads 2
ev set_full_s${s}_full set_full_s$s "full prefix"
ev set_none_s$s set_none_s$s "none"
ev distill_none_s$s distill_none_s$s "none"
echo "g4 phase1 seed $s done $(date)"
