#!/usr/bin/env bash
# RICH-RECEIVER condition (ledger L-181 predictions P1-P3, written before this run): capacity rich7 = at every step one seeded
# receiver decodes 7 packets, the others 1.  Development panel 901-964 x 8/16, eval v6.  Relay students relay_st_s<seed> under the
# default / age-first / bass / hub orders; FO (set_full_s<seed>, fresh-only receiver, raw packets) under default / age-first.
# Usage: bash scripts/RUN_marl_e3_rich_dev.sh <seed>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
s=$1; D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_rich_dev_20260930; mkdir -p "$E"
ev() {  # tag actor-tag checkpoint args...
  local tag=$1 atag=$2 ck=$3; shift 3
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 5 -- "$PY" -u scripts/MARL_e3_delivery_eval_relay_v6.py \
    --actors "$atag=$D/$ck/ckpt_best.pt" "$@" --capacity rich7 --deliveries prefix --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
for o in agefirst hub prefix bass; do ev relay_s${s}_${o} relay_st_s$s relay_st_s$s --relay age --quant 4 --order $o; done
for o in agefirst prefix; do ev FO_s${s}_${o} set_full_s$s set_full_s$s --adapter-override freshonly --order $o; done
echo "rich dev lane $s done $(date)"
