#!/usr/bin/env bash
# PROTOCOL_E3_FALLBACK_MAHAL_20261003.md.  Usage: RUN_marl_e3_fallback_mahal.sh <3x3|4x4> <seed> [<seed> ...]
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
net=$1; shift
if [ "$net" = 3x3 ]; then A=research/marl_budget/e3_delivery_actors_20260929; W=""; ARMS="relayCK1_st relay6Cage_st"; LO=4801
elif [ "$net" = 4x4 ]; then A=research/marl_budget/e3_grid4x4_20260930/actors; W="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"; ARMS="relayCK1_st relayCage_st"; LO=4901
else echo "unknown net $net"; exit 1; fi
F=research/marl_budget/e3_fallback_20261002/$net; P=research/marl_budget/e3_fallback_mahal_20261003/$net; mkdir -p "$P"; SEEDS=$(seq $LO $((LO + 63)))
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
for s in "$@"; do
  for arm in $ARMS; do for K in 1 0 2 3; do
    tag=FBM_${arm}_s${s}_K$K; [ -f "$P/$tag/manifest.json" ] && continue; guard; fresh "$P/$tag"
    "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 900 --retries 3 -- "$PY" -u $W scripts/MARL_e3_fallback_eval_v2.py \
      --relay "$A/${arm}_s$s/ckpt_best.pt" --z "$A/distill_none_s$s/ckpt_best.pt" --calib "$F/cal_${arm}_s$s/calib.json" --K $K \
      --systems FB_S FB_M FB_M95 FB_Mq --parity-relay "$F/FB_${arm}_s${s}_K$K/rows.json" --traffic-seeds $SEEDS --out "$P/$tag" || echo "FAIL $tag"
  done; done
  echo "fallback mahal $net seed $s done $(date)"
done
