#!/usr/bin/env bash
# PROTOCOL_E3_PROTOCOL_CONDITIONED_DEMAND_20261001.md (EXPLORATORY): seeds 0-9 x K in {1,2,3,5,7}, development panel
# seed901-904 x 8/16.  Watchdog-wrapped (CityFlow deadlocks seen 01/10 10:53).  Usage: bash scripts/RUN_marl_e3_protocol_demand.sh <lane 0|1|2>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
A=research/marl_budget/e3_delivery_actors_20260929; O=research/marl_budget/e3_protocol_demand_20261001; mkdir -p "$O"
case $1 in 0) SS="0 3 6 9";; 1) SS="1 4 7";; 2) SS="2 5 8";; esac
for s in $SS; do
  for K in 1 2 3 5 7; do
    tag=s${s}_K$K
    [ -f "$O/$tag/manifest.json" ] && continue
    [ -e "$O/$tag" ] && mv "$O/$tag" "legacy/$(echo "$O/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
    "$PY" scripts/run_with_watchdog.py --log "$O/$tag.log" --out "$O/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_protocol_demand_probe.py \
      --relay "$A/relay6Cage_st_s$s/ckpt_best.pt" --teacher "$A/set_full_s$s/ckpt_best.pt" --K $K --out "$O/$tag" || echo "FAIL $tag"
  done
done
echo "protocol-demand lane $1 done $(date)"
