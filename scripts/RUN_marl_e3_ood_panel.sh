#!/usr/bin/env bash
# PROTOCOL_E3_ROBUST_OOD_20260930.md: seeds 2501-2564 x headways 6/12/24 (used once).  Watchdog on every eval.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_ood_panel_20260930; mkdir -p "$E"; SEEDS=$(seq 2501 2564)
ev() {  # tag actor prog deliveries quant bpp override
  local tag=$1 actor=$2 prog=$3 dels=$4 q=$5 bpp=$6 ov=$7
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  local extra=(); [ "$prog" = v7 ] && extra=(--quant "$q" --byte-capacity "$bpp"); [ -n "$ov" ] && extra+=(--adapter-override "$ov")
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u "scripts/MARL_e3_delivery_eval_$prog.py" --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries $dels --capacity iid \
    ${extra[@]+"${extra[@]}"} --traffic-seeds $SEEDS --headways 6 12 24 --out "$E/$tag" || echo "FAIL $tag"
}
case "$1" in
  A) ev q4t_s0 set_fullq4_s0 v7 prefix 4 3 freshonly; ev ref_distill_none_s0 distill_none_s0 v6 none 0 0 ""; ev ref_set_none_s0 set_none_s0 v6 none 0 0 ""; ev bb_set_full_s0 set_full_s0 v7 prefix 4 3 freshonly;;
  B) ev q4t_s1 set_fullq4_s1 v7 prefix 4 3 freshonly; ev ref_distill_none_s1 distill_none_s1 v6 none 0 0 ""; ev ref_set_none_s1 set_none_s1 v6 none 0 0 ""; ev bb_set_full_s1 set_full_s1 v7 prefix 4 3 freshonly
     [ -f "$E/ref_maxq/manifest.json" ] || "$PY" scripts/run_with_watchdog.py --log "$E/ref_maxq.log" --out "$E/ref_maxq" --stall 300 --retries 3 -- \
       "$PY" -u scripts/MARL_e3_mp2_message_check.py --kinds maxq --deliveries none --traffic-seeds $SEEDS --headways 6 12 24 --out "$E/ref_maxq";;
esac
echo "ood lane $1 done $(date)"
