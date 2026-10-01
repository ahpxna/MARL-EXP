#!/usr/bin/env bash
# PROTOCOL_E3_FRESHONLY addendum 1: the 0-byte distilled student on the NEW panel 2001-2064 x 8/16.  Watchdog.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_freshonly_newpanel_20260929; tag=ref_distill_none_s0
[ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
[ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
"$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
  "$PY" -u scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s0=$D/distill_none_s0/ckpt_best.pt" --deliveries none --capacity iid \
  --traffic-seeds $(seq 2001 2064) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
echo "done $(date)"
