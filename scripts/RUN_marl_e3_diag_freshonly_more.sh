#!/usr/bin/env bash
# D3b (29/09 22:2x), eval-only diagnostics after D3 (L-124/L-125): does the fresh-only receiver rule need the SET actor
# (flat full actors full_s0, full_s1), and does it help set actors trained WITH stale blocks (set_prefix_s0, set_rxq_s0)?
# Every eval under the stall watchdog (stall 300 s, --out, 3 retries); tags d3b_*.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929
JOBS=("d3b_flatfull_freshonly|full_s0=$D/full_s0/ckpt_best.pt full_s1=$D/full_s1/ckpt_best.pt|prefix cap4|iid|freshonly"
      "d3b_setstale_freshonly|set_prefix_s0=$D/set_prefix_s0/ckpt_best.pt set_rxq_s0=$D/set_rxq_s0/ckpt_best.pt|prefix|iid|freshonly")
for j in "${JOBS[@]}"; do
  IFS='|' read -r tag actors dels cap ov <<< "$j"
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_v6.py --actors $actors --deliveries $dels --capacity "$cap" --adapter-override "$ov" \
    --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
done
echo "D3b done $(date)"
