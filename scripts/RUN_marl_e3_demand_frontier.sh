#!/usr/bin/env bash
# PROTOCOL_E3_DEMAND_FRONTIER_20261001.md, panel 2801-2864 x 8/16, used once.  Evaluations only.
# Usage: bash scripts/RUN_marl_e3_demand_frontier.sh <lane 0|1|2>   (seeds split over three lanes)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
lane=$1; D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_demand_frontier_20261001; mkdir -p "$P"
SEEDS=$(seq 2801 2864)
free_gb=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${free_gb:-0}" -lt 15 ] && { echo "REFUSED: ${free_gb} GB free"; exit 1; }
case $lane in 0) SS="0 3 6 9";; 1) SS="1 4 7";; 2) SS="2 5 8";; esac
for s in $SS; do
  tag=Z_s$s
  if [ ! -f "$P/$tag/manifest.json" ]; then
    "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_delivery_eval_v6.py \
      --actors "distill_none_s$s=$D/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
  fi
  for K in 1 2 3 4 5 6 7; do
    tag=R_s${s}_const$K
    [ -f "$P/$tag/manifest.json" ] && continue
    [ -e "$P/$tag" ] && mv "$P/$tag" "legacy/$(echo "$P/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
    "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_delivery_eval_relay_v6.py \
      --actors "relay6Cage_st_s$s=$D/relay6Cage_st_s$s/ckpt_best.pt" --deliveries prefix --capacity const$K --relay age --quant 4 --order agefirst \
      --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
  done
done
echo "demand-frontier lane $lane done $(date)"
