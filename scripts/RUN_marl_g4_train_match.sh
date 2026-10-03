#!/usr/bin/env bash
# PROTOCOL_E3_G4_TRAIN_MATCH_20261002.md (4x4).  Usage: RUN_marl_g4_train_match.sh <seed> [<seed> ...]
# Per seed: train relayCK1_st_s<s> (v9, const1, resumable, 4x4 relay wrapper), then evaluations on panel 4201-4264.  Idempotent.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
A=research/marl_budget/e3_grid4x4_20260930/actors; P=research/marl_budget/e3_g4_train_match_20261002; mkdir -p "$P"
W="scripts/MARL_grid_wrapper.py --rows 4 --cols 4 --"; WR="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
SEEDS=$(seq 4201 4264)
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
run() { local tag=$1; shift; [ -f "$P/$tag/manifest.json" ] && return 0; guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$P/$tag" || echo "FAIL $tag"; }
for s in "$@"; do
  a=relayCK1_st_s$s
  if [ ! -f "$A/$a/manifest.json" ]; then
    guard; echo "train 4x4 $a (v9 const1, resumable) $(date)"
    "$PY" scripts/run_with_watchdog.py --log "$A/$a.log" --stall 1200 --retries 20 -- "$PY" -u $WR scripts/MARL_e3_actor_distill_v9.py \
      --teacher "$A/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age --seed $s --iters 500 --quant 4 --order agefirst \
      --capacity const1 --park-if-no-state --out "$A/$a" || { echo "FAIL $a"; continue; }
  fi
  run Z_s$s $W scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s$s=$A/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16
  for arm in relayCK1_st relayCage_st; do for K in 1 0 2 3; do
    run R_${arm}_s${s}_K$K $WR scripts/MARL_e3_ageclip_eval.py --relay "$A/${arm}_s$s/ckpt_best.pt" --tag ${arm}_s$s --K $K --A -1 --traffic-seeds $SEEDS --headways 8 16
  done; done
  for K in 0 2 3; do
    run J_relayCK1_st_s${s}_K$K $WR scripts/MARL_e3_projection_eval.py --relay "$A/relayCK1_st_s$s/ckpt_best.pt" --tag relayCK1_st_s$s --K $K --A -1 --project onefresh --traffic-seeds $SEEDS --headways 8 16
  done
  echo "4x4 train-match seed $s done $(date)"
done
