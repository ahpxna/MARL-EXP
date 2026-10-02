#!/usr/bin/env bash
# PROTOCOL_E3_WHOLE_FIBRE_PILOT_20261001.md: seeds 1 and 8, two shards each.  Diagnostic probe, development panel.
# Usage: bash scripts/RUN_marl_e3_whole_fibre.sh <seed> <shard>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
s=$1; sh=$2; A=research/marl_budget/e3_delivery_actors_20260929; O=research/marl_budget/e3_whole_fibre_20261001/s$s
mkdir -p "$O"
"$PY" -u scripts/MARL_e3_whole_fibre_probe.py --seed "$s" --relay "$A/relay6Cage_st_s$s/ckpt_best.pt" --teacher "$A/set_full_s$s/ckpt_best.pt" \
  --parity "research/marl_budget/e3_satrot_eval_20260930/relay6Cage_st_s${s}_agefirst_low/rows.json" --shard "$sh" --nshards 2 --out "$O" \
  > "$O/shard$sh.log" 2>&1 || echo "FAIL s$s shard $sh"
echo "whole-fibre s$s shard $sh done $(date)"
