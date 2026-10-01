#!/usr/bin/env bash
# PROTOCOL_E3_TRAINEDQ4_20260930.md, panel 2401-2464 x 8/16 (used once).  Watchdog on every eval.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_trainedq4_panel_20260930; mkdir -p "$E"; SEEDS=$(seq 2401 2464)
ev() {  # tag actor prog deliveries quant bpp override
  local tag=$1 actor=$2 prog=$3 dels=$4 q=$5 bpp=$6 ov=$7
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag"; return 0; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  local extra=(); [ "$prog" = v7 ] && extra=(--quant "$q" --byte-capacity "$bpp"); [ -n "$ov" ] && extra+=(--adapter-override "$ov")
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u "scripts/MARL_e3_delivery_eval_$prog.py" --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries $dels --capacity iid \
    ${extra[@]+"${extra[@]}"} --traffic-seeds $SEEDS --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
for s in 0 1; do
  ev q4t_s$s set_fullq4_s$s v7 prefix 4 3 freshonly
  ev ref_distill_none_s$s distill_none_s$s v6 none 0 0 ""
  ev ref_set_none_s$s set_none_s$s v6 none 0 0 ""
  ev bb_set_full_s$s set_full_s$s v7 prefix 4 3 freshonly
done
if [ ! -f "$E/ref_maxq/manifest.json" ]; then
  "$PY" scripts/run_with_watchdog.py --log "$E/ref_maxq.log" --out "$E/ref_maxq" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_mp2_message_check.py --kinds maxq --deliveries none --traffic-seeds $SEEDS --headways 8 16 --out "$E/ref_maxq" || echo "FAIL maxq"
fi
echo "trainedq4 panel done $(date)"
