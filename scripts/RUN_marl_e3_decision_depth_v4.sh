#!/usr/bin/env bash
# PROTOCOL_E3_EXACT_DEMAND_1B_20261001.md: v4 probes (exhaustive subsets, empty + cache bases), development panel
# seed901-916 x 8/16, ten seeds over three lanes.  Usage: bash scripts/RUN_marl_e3_decision_depth_v4.sh <lane 0|1|2>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
A=research/marl_budget/e3_delivery_actors_20260929; O=research/marl_budget/e3_decision_depth_v4_20261001; mkdir -p "$O"
case $1 in 0) SS="0 3 6 9";; 1) SS="1 4 7";; 2) SS="2 5 8";; esac
for s in $SS; do
  [ -f "$O/cage_s$s/manifest.json" ] && continue
  [ -e "$O/cage_s$s" ] && mv "$O/cage_s$s" "legacy/$(echo "$O/cage_s$s" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  "$PY" -u scripts/MARL_e3_decision_depth_probe_v4.py --relay "$A/relay6Cage_st_s$s/ckpt_best.pt" --teacher "$A/set_full_s$s/ckpt_best.pt" \
    --parity "research/marl_budget/e3_satrot_eval_20260930/relay6Cage_st_s${s}_agefirst_low/rows.json" --out "$O/cage_s$s" \
    > "$O/cage_s$s.log" 2>&1 || echo "FAIL cage_s$s"
done
echo "v4 lane $1 done $(date)"
