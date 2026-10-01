#!/usr/bin/env bash
# PROTOCOL_E3_FRESHONLY_20260929.md, training seed 0 on the NEW panel 2001-2064 x 8/16 (used once).  Watchdog on every eval.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_freshonly_newpanel_20260929; mkdir -p "$E"
JOBS=("fo_set_full_s0|set_full_s0=$D/set_full_s0/ckpt_best.pt|prefix cap4|freshonly"
      "def_set_full_s0|set_full_s0=$D/set_full_s0/ckpt_best.pt|prefix full|default"
      "ref_set_none_s0|set_none_s0=$D/set_none_s0/ckpt_best.pt|none|default"
      "ref_set_prefix_s0|set_prefix_s0=$D/set_prefix_s0/ckpt_best.pt|prefix|default")
for j in "${JOBS[@]}"; do
  IFS='|' read -r tag actors dels ov <<< "$j"
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_v6.py --actors $actors --deliveries $dels --capacity iid --adapter-override "$ov" \
    --traffic-seeds $(seq 2001 2064) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
done
echo "newpanel s0 done $(date)"
