#!/usr/bin/env bash
# V-D10 (PROTOCOL_E3_DECISION_DEPTH_TEN_SEEDS_20261001.md): decision-depth probe, relay6Cage_st_s<s>, agefirst, low.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_decision_depth_ten_20261001; P=research/marl_budget/e3_satrot_eval_20260930
mkdir -p "$E"
for s in "$@"; do
  tag=cage_s${s}_agefirst_low
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "probe $tag $(date)"
  nice -n 5 "$PY" -u scripts/MARL_e3_decision_depth_probe.py --relay "$D/relay6Cage_st_s$s/ckpt_best.pt" --teacher "$D/set_full_s$s/ckpt_best.pt" \
    --order agefirst --rule prefix --capacity low --traffic-seeds $(seq 901 964) --headways 8 16 \
    --parity "$P/relay6Cage_st_s${s}_agefirst_low/rows.json" --out "$E/$tag" > "$E/$tag.log" 2>&1 || echo "FAIL $tag"
  tail -1 "$E/$tag.log"
done
echo "ALL DONE $* $(date)"
