#!/usr/bin/env bash
# PROTOCOL_E3_G4_MIX_20261002.md (test D, 4x4).  Usage: RUN_marl_g4_mix.sh <seed> [<seed> ...]   (panel 4601-4664)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
A=research/marl_budget/e3_grid4x4_20260930/actors; P=research/marl_budget/e3_g4_mix_20261002; mkdir -p "$P"; SEEDS=$(seq 4601 4664)
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
run() { local tag=$1; shift; [ -f "$P/$tag/manifest.json" ] && return 0; guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$P/$tag" || echo "FAIL $tag"; }
for s in "$@"; do
  a=relayMIX_st_s$s
  if [ ! -f "$A/$a/manifest.json" ]; then
    guard; echo "train 4x4 $a (v11 mix, resumable) $(date)"
    "$PY" scripts/run_with_watchdog.py --log "$A/$a.log" --stall 1200 --retries 20 -- "$PY" -u scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 -- \
      scripts/MARL_e3_actor_distill_v11.py --teacher "$A/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age --seed $s --iters 500 \
      --quant 4 --order agefirst --capacity mix --park-if-no-state --out "$A/$a" || { echo "FAIL $a"; continue; }
  fi
  run Z_s$s scripts/MARL_grid_wrapper.py --rows 4 --cols 4 -- scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s$s=$A/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16
  for arm in relayMIX_st relayCage_st relayCK1_st; do for K in 1 0 2 3; do
    run R_${arm}_s${s}_K$K scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 -- scripts/MARL_e3_ageclip_eval.py --relay "$A/${arm}_s$s/ckpt_best.pt" --tag ${arm}_s$s --K $K --A -1 --traffic-seeds $SEEDS --headways 8 16
  done; done
  echo "4x4 mix seed $s done $(date)"
done
