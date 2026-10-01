#!/usr/bin/env bash
# PROTOCOL_E3_TEN_SEEDS_20260930.md (ledger L-186), panel 2701-2764 x 8/16, used once.  Evaluations only.
# Usage: bash scripts/RUN_marl_e3_ten_seed_panel.sh <lane 0|1>   (lane 0: seeds 0-4, lane 1: seeds 5-9)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
lane=$1; D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_ten_seed_panel_20260930; mkdir -p "$P"
SEEDS=$(seq 2701 2764)
evr() {  # tag actor order capacity deliveries
  local tag=$1 actor=$2 order=$3 cap=$4 dels=$5
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag (no $actor)"; return 0; }
  [ -f "$P/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$P/$tag" ] && mv "$P/$tag" "legacy/$(echo "$P/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_delivery_eval_relay_satrot.py \
    --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries $dels --capacity "$cap" --relay age --quant 4 --order "$order" \
    --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
}
evz() {  # tag actor
  local tag=$1 actor=$2
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag (no $actor)"; return 0; }
  [ -f "$P/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_delivery_eval_v6.py \
    --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
}
if [ "$lane" = 0 ]; then SS="0 1 2 3 4"; else SS="5 6 7 8 9"; fi
for s in $SS; do
  evz Z_s$s distill_none_s$s
  evr C_s${s}_agefirst_iid relay6Cage_st_s$s agefirst iid "prefix cap4"
  evr C_s${s}_agefirst_low relay6Cage_st_s$s agefirst low "prefix"
done
for s in $SS; do
  evz Zrep_s$s distill_none_rep_s$s
  evr C_s${s}_prefix_iid relay6Cage_st_s$s prefix iid "prefix cap4"
  evr C_s${s}_prefix_low relay6Cage_st_s$s prefix low "prefix"
done
echo "ten-seed panel lane $lane done $(date)"
