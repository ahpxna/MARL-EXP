#!/usr/bin/env bash
# Music-theory broadcast orders for the relay students (30/09 13:2x EDT; ledger L-168).  Development panel 901-964 x 8/16.
# Usage: bash scripts/RUN_marl_e3_music_eval.sh <seed>      (one lane per relay student seed)
# Pre-registered reading rule: ledger L-168 (written before this script ran).
set -u
cd "$(dirname "$0")/.."
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
s=$1; D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_music_eval_20260930; mkdir -p "$E"
ev() {  # tag order capacity deliveries...
  local tag=$1 order=$2 cap=$3; shift 3
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 5 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_relay_v3.py --actors "relay_st_s$s=$D/relay_st_s$s/ckpt_best.pt" --deliveries "$@" \
    --capacity "$cap" --relay age --quant 4 --order "$order" --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
ev relay_st_s${s}_bass_iid bass iid prefix cap4
ev relay_st_s${s}_agefirst_iid agefirst iid prefix cap4
ev relay_st_s${s}_prefix_low prefix low prefix
ev relay_st_s${s}_bass_low bass low prefix
ev relay_st_s${s}_agefirst_low agefirst low prefix
echo "LANE $s DONE $(date)"
