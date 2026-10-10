#!/usr/bin/env bash
# PROTOCOL_E3_JOINT_THROTTLE_20261003.md.  Usage: RUN_marl_e3_joint_throttle.sh <3x3|4x4> <seed> [<seed> ...]
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
net=$1; shift
if [ "$net" = 3x3 ]; then A=research/marl_budget/e3_delivery_actors_20260929; W=""; ZW=""; CAGE=relay6Cage_st
elif [ "$net" = 4x4 ]; then A=research/marl_budget/e3_grid4x4_20260930/actors; W="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
  ZW="scripts/MARL_grid_wrapper.py --rows 4 --cols 4 --"; CAGE=relayCage_st
else echo "unknown net $net"; exit 1; fi
if [ "${SMOKE:-0}" = 1 ]; then P=research/marl_budget/e3_joint_throttle_20261003/smoke_pipe/$net; SEEDS="9001 9002"
else P=research/marl_budget/e3_joint_throttle_20261003/$net; SEEDS=$(seq 5201 5264); fi
mkdir -p "$P"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
wd() { local tag=$1; shift; [ -f "$P/$tag/manifest.json" ] && return 0; guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$P/$tag" || echo "FAIL $tag"; }
for s in "$@"; do
  wd Z_s$s $ZW scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s$s=$A/distill_none_s$s/ckpt_best.pt" --deliveries none \
    --capacity iid --traffic-seeds $SEEDS --headways 8 16
  for K in 0 1 2 3; do
    wd JT_relayCK1_st_s${s}_K$K $W scripts/MARL_e3_joint_throttle_eval.py --relay "$A/relayCK1_st_s$s/ckpt_best.pt" --tag relayCK1_st_s$s \
      --K $K --ktrain 1 --traffic-seeds $SEEDS --headways 8 16
  done
  for K in 0 1; do
    wd JT_${CAGE}_s${s}_K$K $W scripts/MARL_e3_joint_throttle_eval.py --relay "$A/${CAGE}_s$s/ckpt_best.pt" --tag ${CAGE}_s$s \
      --K $K --modes plain mask --traffic-seeds $SEEDS --headways 8 16
  done
  echo "joint throttle $net seed $s done $(date)"
done
