#!/usr/bin/env bash
# PROTOCOL_E3_RELAY_ROTATION_20260930.md, panel 2601-2664 x 8/16 (used once).  Watchdog on every eval.
# Usage: bash scripts/RUN_marl_e3_relayrot_panel.sh <seed>     (one lane per training seed)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
s=$1; D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_relayrot_panel_20260930; mkdir -p "$E"
SEEDS=$(seq 2601 2664)
run() {  # tag actor cmd...
  local tag=$1 actor=$2; shift 2
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag (no actor)"; return 0; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 5 -- "$PY" -u "$@" \
    --actors "$actor=$D/$actor/ckpt_best.pt" --traffic-seeds $SEEDS --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
RELAY=(scripts/MARL_e3_delivery_eval_relay_satrot.py --relay age --quant 4)
# PRIMARY arm: relay + agefirst, conditions C1+C2 (iid) and C3 (low)
run relay_st_s${s}_agefirst_iid relay_st_s$s "${RELAY[@]}" --order agefirst --capacity iid --deliveries prefix cap4
run relay_st_s${s}_agefirst_low relay_st_s$s "${RELAY[@]}" --order agefirst --capacity low --deliveries prefix
# PRIMARY comparator: the 0-byte distilled student
run ref_distill_none_s$s distill_none_s$s scripts/MARL_e3_delivery_eval_v6.py --deliveries none --capacity iid
# secondary: prefix-order relay, BYTEBUDGET, set_none
run relay_st_s${s}_prefix_iid relay_st_s$s "${RELAY[@]}" --order prefix --capacity iid --deliveries prefix cap4
run relay_st_s${s}_prefix_low relay_st_s$s "${RELAY[@]}" --order prefix --capacity low --deliveries prefix
run bb_set_full_s$s set_full_s$s scripts/MARL_e3_delivery_eval_v7.py --quant 4 --byte-capacity 3 --adapter-override freshonly --deliveries prefix --capacity iid
run ref_set_none_s$s set_none_s$s scripts/MARL_e3_delivery_eval_v6.py --deliveries none --capacity iid
if [ "$s" = 0 ] && [ ! -f "$E/ref_maxq/manifest.json" ]; then
  "$PY" scripts/run_with_watchdog.py --log "$E/ref_maxq.log" --out "$E/ref_maxq" --stall 300 --retries 5 -- \
    "$PY" -u scripts/MARL_e3_mp2_message_check.py --kinds maxq --deliveries none --traffic-seeds $SEEDS --headways 8 16 --out "$E/ref_maxq" || echo "FAIL maxq"
fi
echo "relayrot panel lane $s done $(date)"
