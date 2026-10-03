#!/usr/bin/env bash
# PROTOCOL_E3_HOLD_PROSPECTIVE_20261001.md: panel 3501-3564 x 8/16 (used once).  Usage: bash scripts/RUN_marl_e3_hold_prospective.sh <lane 0|1|2>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
lane=$1; D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_hold_prospective_20261001; mkdir -p "$P"
SEEDS=$(seq 3501 3564)
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 10 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
run() { local tag=$1; shift; [ -f "$P/$tag/manifest.json" ] && return 0; guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u "$@" --out "$P/$tag" || echo "FAIL $tag"; }
case $lane in 0) SS="0 3 6 9";; 1) SS="1 4 7";; 2) SS="2 5 8";; esac
for s in $SS; do
  run Z_s$s scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s$s=$D/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16
  for cfg in 2:1 2:3 2:4 2:6 3:1 3:6; do
    K=${cfg%%:*}; r=${cfg##*:}
    run R_s${s}_K${K}_r$r scripts/MARL_e3_hold_eval.py --relay "$D/relay6Cage_st_s$s/ckpt_best.pt" --tag relay6Cage_st_s$s --hold $r --K $K --A -1 --traffic-seeds $SEEDS --headways 8 16
  done
done
echo "hold-prospective lane $lane done $(date)"
