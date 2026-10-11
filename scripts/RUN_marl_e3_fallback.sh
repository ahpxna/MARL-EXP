#!/usr/bin/env bash
# PROTOCOL_E3_SUPPORT_FALLBACK_20261002.md (02/10/2026 22:3x EDT; nyc branch 22:4x).  Usage: RUN_marl_e3_fallback.sh <3x3|4x4|nyc> <seed> [<seed> ...]
# Per seed: Z on the panel (once; every cell reuses it), then per receiver arm: calibration on its training episodes 301-332 under
# its training channel, and the fallback cells K in {1, 2, 3, iid}.  SMOKE=1: 2 panel traffic seeds, calibration 301-302,
# output under e3_fallback_20261002/smoke_pipe.  Watchdog on every run; finished items are skipped (resumable).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
net=$1; shift
if [ "$net" = 3x3 ]; then A=research/marl_budget/e3_delivery_actors_20260929; W=""; ARMS="relay6Cage_st relayCK1_st relayMIX_st relayMIX2_st"; SYS="FB_S FB_S1 FB_S10 FB_F FB_R"; LO=4801
elif [ "$net" = 4x4 ]; then A=research/marl_budget/e3_grid4x4_20260930/actors; W="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"; ARMS="relayCage_st relayCK1_st"; SYS="FB_S FB_F FB_R"; LO=4901
elif [ "$net" = nyc ]; then A=${NYC_ACTORS:-research/marl_budget/e3_nyc16x3_20261002/actors}; W="scripts/MARL_nyc_wrapper.py --relay-slots nearest8 --"; ARMS="relayCage_st relayCK1_st"; SYS="FB_S FB_F FB_R"; LO=5001
else echo "unknown net $net"; exit 1; fi
if [ "${SMOKE:-0}" = 1 ]; then P=research/marl_budget/e3_fallback_20261002/${SMOKE_DIR:-smoke_pipe}/$net; SEEDS="$LO $((LO + 1))"; CH=302
else P=research/marl_budget/e3_fallback_20261002/$net; SEEDS=$(seq $LO $((LO + 63))); CH=332; fi
mkdir -p "$P"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
run() { local tag=$1; shift; [ -f "$P/$tag/manifest.json" ] && return 0; guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 900 --retries 3 -- "$PY" -u ${W:+$W} scripts/MARL_e3_fallback_eval.py "$@" --out "$P/$tag" || echo "FAIL $tag"; }
for s in "$@"; do
  run Z_s$s --z-only --z "$A/distill_none_s$s/ckpt_best.pt" --traffic-seeds $SEEDS
  for arm in $ARMS; do
    run cal_${arm}_s$s --calibrate --relay "$A/${arm}_s$s/ckpt_best.pt" --calib-lo 301 --calib-hi $CH
    [ -f "$P/cal_${arm}_s$s/calib.json" ] || { echo "FAIL no calibration ${arm}_s$s"; continue; }
    for K in 1 2 3 0; do
      run FB_${arm}_s${s}_K$K --relay "$A/${arm}_s$s/ckpt_best.pt" --z "$A/distill_none_s$s/ckpt_best.pt" --calib "$P/cal_${arm}_s$s/calib.json" \
        --K $K --systems $SYS --traffic-seeds $SEEDS
    done
  done
  echo "fallback $net seed $s done $(date)"
done
