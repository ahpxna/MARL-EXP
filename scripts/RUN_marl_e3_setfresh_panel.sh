#!/usr/bin/env bash
# PROTOCOL_E3_SETFRESH_20260929.md, panel 2301-2364 x 8/16 (used once).  Unfinished checkpoints are skipped (rerun later).
# Watchdog on every eval.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_setfresh_panel_20260929; mkdir -p "$E"; SEEDS=$(seq 2301 2364)
JOBS=("sf_s0|set_fresh_s0|prefix cap4" "ref_distill_none_s0|distill_none_s0|none" "ref_set_none_s0|set_none_s0|none" "ref_set_prefix_s0|set_prefix_s0|prefix" "st_fo_s0|distill_fo_prefix_s0|prefix"
      "sf_s1|set_fresh_s1|prefix cap4" "ref_distill_none_s1|distill_none_s1|none" "ref_set_none_s1|set_none_s1|none" "ref_set_prefix_s1|set_prefix_s1|prefix" "st_fo_s1|distill_fo_prefix_s1|prefix")
for j in "${JOBS[@]}"; do
  IFS='|' read -r tag actor dels <<< "$j"
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag ($actor not finished)"; continue; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_v6.py --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries $dels --capacity iid \
    --traffic-seeds $SEEDS --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
done
if [ ! -f "$E/ref_maxq/manifest.json" ]; then
  [ -e "$E/ref_maxq" ] && mv "$E/ref_maxq" "legacy/$(echo "$E/ref_maxq" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  "$PY" scripts/run_with_watchdog.py --log "$E/ref_maxq.log" --out "$E/ref_maxq" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_mp2_message_check.py --kinds maxq --deliveries none --traffic-seeds $SEEDS --headways 8 16 --out "$E/ref_maxq" || echo "FAIL maxq"
fi
echo "setfresh panel pass done $(date)"
