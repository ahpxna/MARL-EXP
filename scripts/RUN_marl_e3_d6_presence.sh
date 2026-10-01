#!/usr/bin/env bash
# D6 (29/09 23:1x), eval-only: how many ABSENT senders break the flat actor?  Flat full-delivery actors (full_s0, full_s1)
# with the fresh-only receiver under capacities 5-7 of 8 (--capacity high).  The set actor set_full_s0 is already measured
# (d3w_setfull_high_freshonly: 1182.3, equal to full).  Watchdog on every eval; development panel 901-964 x 8/16.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929; tag=d6_flatfull_high_freshonly
[ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
[ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
"$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
  "$PY" -u scripts/MARL_e3_delivery_eval_v6.py --actors "full_s0=$D/full_s0/ckpt_best.pt" "full_s1=$D/full_s1/ckpt_best.pt" \
  --deliveries prefix --capacity high --adapter-override freshonly --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
echo "D6 done $(date)"
