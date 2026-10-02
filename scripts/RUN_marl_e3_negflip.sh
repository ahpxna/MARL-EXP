#!/usr/bin/env bash
# PROTOCOL_E3_NEGFLIP_VS_Z_20261001.md (EXPLORATORY): development panel seed901-904 x 8/16, K in {0 = iid, 1, 2, 3}.
# Usage: bash scripts/RUN_marl_e3_negflip.sh <lane 0|1>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
lane=$1; D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_negflip_20261001; mkdir -p "$P"
case $lane in 0) SS="0 2 4 6 8";; 1) SS="1 3 5 7 9";; esac
for s in $SS; do
  for K in 1 2 3 0; do
    tag=s${s}_K$K
    [ -f "$P/$tag/manifest.json" ] && continue
    [ -e "$P/$tag" ] && mv "$P/$tag" "legacy/$(echo "$P/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
    "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_negflip_probe.py \
      --relay "$D/relay6Cage_st_s$s/ckpt_best.pt" --teacher "$D/set_full_s$s/ckpt_best.pt" --z "$D/distill_none_s$s/ckpt_best.pt" \
      --zrows "research/marl_budget/e3_dev_Z_20261001/Z_s$s/rows.json" --K $K --out "$P/$tag" || echo "FAIL $tag"
  done
done
echo "negflip lane $lane done $(date)"
