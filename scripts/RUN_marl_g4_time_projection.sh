#!/usr/bin/env bash
# PROTOCOL_E3_G4_TIME_PROJECTION_20261002.md.  Usage: RUN_marl_g4_time_projection.sh <seed> [<seed> ...]   (4x4, panel 4301-4364)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
A=research/marl_budget/e3_grid4x4_20260930/actors; P=research/marl_budget/e3_g4_time_projection_20261002; mkdir -p "$P"
T=research/marl_budget/e3_g4_coverage_time_table_iid_20261002.json; SEEDS=$(seq 4301 4364)
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
run() { local tag=$1; shift; [ -f "$P/$tag/manifest.json" ] && return 0; guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$P/$tag" || echo "FAIL $tag"; }
for s in "$@"; do
  run Z_s$s scripts/MARL_grid_wrapper.py --rows 4 --cols 4 -- scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s$s=$A/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16
  for K in 1 0; do
    run P_s${s}_K$K scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 -- scripts/MARL_e3_projection_eval_v2.py --relay "$A/relayCage_st_s$s/ckpt_best.pt" --tag relayCage_st_s$s --K $K --A -1 --traffic-seeds $SEEDS --headways 8 16
    run T_s${s}_K$K scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 -- scripts/MARL_e3_projection_eval_v2.py --relay "$A/relayCage_st_s$s/ckpt_best.pt" --tag relayCage_st_s$s --K $K --A -1 --project timecov --table $T --traffic-seeds $SEEDS --headways 8 16
  done
  echo "time projection seed $s done $(date)"
done
