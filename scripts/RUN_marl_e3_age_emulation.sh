#!/usr/bin/env bash
# PROTOCOL_E3_AGE_EMULATION_20261003.md (03/10/2026 03:0x EDT; reviewer G2 / H1).  Usage: RUN_marl_e3_age_emulation.sh <3x3|4x4> <seed> [<seed> ...]
# Per seed: Z on panel 5101-5164 x 8/16; per receiver arm: rank-wise age floors from its own training channel (calibration seeds
# 301-332 x 8/16), then PLAIN / EMU / LAB in one process per capacity cell.  Watchdog on every run; finished items are skipped.
# SMOKE=1: traffic seeds 9001-9002, calibration 301-302, output under e3_age_emulation_20261003/smoke_pipe.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
net=$1; shift
if [ "$net" = 3x3 ]; then A=research/marl_budget/e3_delivery_actors_20260929; W=""; ZW=""; CAGE=relay6Cage_st
elif [ "$net" = 4x4 ]; then A=research/marl_budget/e3_grid4x4_20260930/actors; W="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
  ZW="scripts/MARL_grid_wrapper.py --rows 4 --cols 4 --"; CAGE=relayCage_st
else echo "unknown net $net"; exit 1; fi
if [ "${SMOKE:-0}" = 1 ]; then P=research/marl_budget/e3_age_emulation_20261003/smoke_pipe/$net; SEEDS="9001 9002"; CH=302
else P=research/marl_budget/e3_age_emulation_20261003/$net; SEEDS=$(seq 5101 5164); CH=332; fi
mkdir -p "$P"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
wd() { local tag=$1; shift; [ -f "$P/$tag/manifest.json" ] && return 0; guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$P/$tag" || echo "FAIL $tag"; }
for s in "$@"; do
  wd Z_s$s $ZW scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s$s=$A/distill_none_s$s/ckpt_best.pt" --deliveries none \
    --capacity iid --traffic-seeds $SEEDS --headways 8 16
  for spec in "relayCK1_st 1 1 0 2 3" "$CAGE 0 0"; do
    set -- $spec; arm=$1; ck=$2; shift 2; R="$A/${arm}_s$s/ckpt_best.pt"
    wd cal_${arm}_s$s $W scripts/MARL_e3_age_emulation_eval.py --relay "$R" --tag ${arm}_s$s --calibrate --calib-K $ck \
      --calib-lo 301 --calib-hi $CH --headways 8 16
    [ -f "$P/cal_${arm}_s$s/floors.json" ] || { echo "FAIL no floors ${arm}_s$s"; continue; }
    for K in "$@"; do
      wd EM_${arm}_s${s}_K$K $W scripts/MARL_e3_age_emulation_eval.py --relay "$R" --tag ${arm}_s$s \
        --floors "$P/cal_${arm}_s$s/floors.json" --K $K --zero-floor-check --traffic-seeds $SEEDS --headways 8 16
    done
  done
  echo "age emulation $net seed $s done $(date)"
done
