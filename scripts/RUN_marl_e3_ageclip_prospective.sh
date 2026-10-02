#!/usr/bin/env bash
# PROTOCOL_E3_AGECLIP_PROSPECTIVE_20261001.md, panel 3101-3164 x 8/16, used once.  Evaluations only.
# Usage: bash scripts/RUN_marl_e3_ageclip_prospective.sh <lane 0|1|2>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
lane=$1; D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_ageclip_prospective_20261001; mkdir -p "$P"
SEEDS=$(seq 3101 3164)
free_gb=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${free_gb:-0}" -lt 15 ] && { echo "REFUSED: ${free_gb} GB free"; exit 1; }
case $lane in 0) SS="0 3 6 9";; 1) SS="1 4 7";; 2) SS="2 5 8";; esac
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
for s in $SS; do
  tag=Z_s$s
  if [ ! -f "$P/$tag/manifest.json" ]; then
    fresh "$P/$tag"
    "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_delivery_eval_v6.py \
      --actors "distill_none_s$s=$D/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
  fi
  for K in 1 0; do
    for A in 2 -1; do
      tag=R_s${s}_K${K}_A$A
      [ -f "$P/$tag/manifest.json" ] && continue
      fresh "$P/$tag"
      "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_ageclip_eval.py \
        --relay "$D/relay6Cage_st_s$s/ckpt_best.pt" --tag relay6Cage_st_s$s --K $K --A $A --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
    done
  done
done
echo "ageclip-prospective lane $lane done $(date)"
