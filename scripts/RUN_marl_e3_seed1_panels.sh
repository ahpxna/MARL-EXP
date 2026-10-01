#!/usr/bin/env bash
# Seed-1 evaluations for PROTOCOL_E3_FRESHONLY (+ addendum 1; panel 2001-2064) and PROTOCOL_E3_BYTEBUDGET (panel 2101-2164),
# written 23:2x before any seed-1 run on these panels.  Jobs whose checkpoint does not exist yet are skipped (rerun later;
# finished jobs are skipped by their manifest).  Watchdog on every eval.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; FO=research/marl_budget/e3_freshonly_newpanel_20260929; BB=research/marl_budget/e3_bytebudget_panel_20260929
# dir|tag|actor|deliveries|adapter|quant|bpp|seeds
JOBS=("$FO|ref_set_none_s1|set_none_s1|none|default|0|0|2001"
      "$FO|ref_set_prefix_s1|set_prefix_s1|prefix|default|0|0|2001"
      "$FO|fo_set_full_s1|set_full_s1|prefix cap4|freshonly|0|0|2001"
      "$FO|def_set_full_s1|set_full_s1|prefix full|default|0|0|2001"
      "$FO|ref_distill_none_s1|distill_none_s1|none|default|0|0|2001"
      "$BB|ref_set_none_s1|set_none_s1|none|default|0|0|2101"
      "$BB|var_set_full_s1|set_full_s1|prefix|freshonly|4|3|2101"
      "$BB|raw_set_full_s1|set_full_s1|full|default|0|0|2101"
      "$BB|ref_distill_none_s1|distill_none_s1|none|default|0|0|2101")
for j in "${JOBS[@]}"; do
  IFS='|' read -r E tag actor dels ov q bpp s0 <<< "$j"
  ck="$D/$actor/ckpt_best.pt"
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag ($actor not finished)"; continue; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $E/$tag"; continue; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $E/$tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_v7.py --actors "$actor=$ck" --deliveries $dels --capacity iid --adapter-override "$ov" \
    --quant "$q" --byte-capacity "$bpp" --traffic-seeds $(seq "$s0" $((s0 + 63))) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
done
echo "seed-1 panels pass done $(date)"
