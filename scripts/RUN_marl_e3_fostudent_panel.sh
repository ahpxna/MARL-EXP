#!/usr/bin/env bash
# PROTOCOL_E3_FOSTUDENT_20260929.md, panel 2201-2264 x 8/16 (used once).  Jobs whose checkpoint is not finished are skipped
# (rerun the script later; finished jobs are skipped by their manifest).  Watchdog on every eval.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_fostudent_panel_20260929; mkdir -p "$E"
SEEDS=$(seq 2201 2264)
# tag|actor|deliveries|quant|bpp|adapter-override
JOBS=("st_fo_s0|distill_fo_prefix_s0|prefix cap4|0|0|" "ref_distill_none_s0|distill_none_s0|none|0|0|" "ref_set_none_s0|set_none_s0|none|0|0|"
      "bb_set_full_s0|set_full_s0|prefix|4|3|freshonly"
      "st_fo_s1|distill_fo_prefix_s1|prefix cap4|0|0|" "ref_distill_none_s1|distill_none_s1|none|0|0|" "ref_set_none_s1|set_none_s1|none|0|0|"
      "bb_set_full_s1|set_full_s1|prefix|4|3|freshonly")
for j in "${JOBS[@]}"; do
  IFS='|' read -r tag actor dels q bpp ov <<< "$j"
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag ($actor not finished)"; continue; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  OV=(); [ -n "$ov" ] && OV=(--adapter-override "$ov")
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_v7.py --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries $dels --capacity iid ${OV[@]+"${OV[@]}"} \
    --quant "$q" --byte-capacity "$bpp" --traffic-seeds $SEEDS --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
done
[ -f "$E/ref_maxq/manifest.json" ] || { [ -e "$E/ref_maxq" ] && mv "$E/ref_maxq" "legacy/$(echo "$E/ref_maxq" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)";
  "$PY" scripts/run_with_watchdog.py --log "$E/ref_maxq.log" --out "$E/ref_maxq" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_mp2_message_check.py --kinds maxq --deliveries none --traffic-seeds $SEEDS --headways 8 16 --out "$E/ref_maxq" || echo "FAIL maxq"; }
echo "fostudent panel pass done $(date)"
