#!/usr/bin/env bash
# 128-episode evaluations (901-964 x 8/16, iid capacities) of finished trainings named on the command line (29/09 22:3x).
# Every eval under the stall watchdog (stall 300 s, --out, 3 retries).  Deliveries per tag from the table below.
# Usage: bash scripts/RUN_marl_e3_eval_tags.sh tag [tag ...]
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929
dels_of() {
  case "$1" in
    rc_noise_s0|distill_none_s0) echo "none";;
    rc_fresh_s0|rc_sconcat_s0|rc_attn_s0|rc_h256_s0|set_prefix_s1) echo "prefix none";;
    set_none_s1) echo "none prefix";;
    set_rxq_s1) echo "rxq prefix none";;
    set_full_s1) echo "full prefix none";;
    distill_prefix_s0) echo "prefix none";;
    distill_rxq_s0) echo "rxq prefix none";;
    *) echo "";;
  esac
}
for tag in "$@"; do
  dels="$(dels_of "$tag")"; [ -z "$dels" ] && { echo "UNKNOWN $tag"; continue; }
  [ -f "$D/$tag/manifest.json" ] || { echo "NOT FINISHED $tag"; continue; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag ($dels) $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_v6.py --actors "$tag=$D/$tag/ckpt_best.pt" --deliveries $dels --capacity iid \
    --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
done
echo "evals done $(date)"
