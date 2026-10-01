#!/usr/bin/env bash
# PROTOCOL_E3_BYTEBUDGET_20260929.md, training seed 0, panel 2101-2164 x 8/16 (used once).  Watchdog on every eval.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_bytebudget_panel_20260929; mkdir -p "$E"
JOBS=("var_set_full_s0|set_full_s0=$D/set_full_s0/ckpt_best.pt|prefix|freshonly|4|3"
      "ref_distill_none_s0|distill_none_s0=$D/distill_none_s0/ckpt_best.pt|none|default|0|0"
      "ref_set_none_s0|set_none_s0=$D/set_none_s0/ckpt_best.pt|none|default|0|0"
      "raw_set_full_s0|set_full_s0=$D/set_full_s0/ckpt_best.pt|full|default|0|0")
for j in "${JOBS[@]}"; do
  IFS='|' read -r tag actors dels ov q bpp <<< "$j"
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_v7.py --actors $actors --deliveries $dels --capacity iid --adapter-override "$ov" \
    --quant "$q" --byte-capacity "$bpp" --traffic-seeds $(seq 2101 2164) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
done
echo "bytebudget s0 done $(date)"
