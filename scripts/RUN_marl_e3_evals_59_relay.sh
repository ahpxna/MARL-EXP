#!/usr/bin/env bash
# Development-panel evals (901-964 x 8/16) for seeds 5-9 (L-161) and the relay method (L-162).  Unfinished checkpoints are
# skipped, so the script is rerun as runs finish.  Watchdog on every eval.
#  seeds 5-9: set_none_sN (none), set_full_sN (full prefix none), bb_set_full_sN (eval-only 3 B byte budget), distill_none_sN (none)
#  relay:     relay_st_sN, relay_ppo_sN under the UNCHANGED packet channel with relay-merged 3 B packets (prefix and cap4),
#             and with no messages (none).  Evaluator scripts/MARL_e3_delivery_eval_relay.py --relay age --quant 4.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929; SEEDS=$(seq 901 964)
ev() {  # tag actor prog deliveries extra-args...
  local tag=$1 actor=$2 prog=$3 dels=$4; shift 4
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag"; return 0; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u "scripts/MARL_e3_delivery_eval_$prog.py" --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries $dels --capacity iid \
    "$@" --traffic-seeds $SEEDS --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
for s in 0 1; do
  ev relay_st_s${s}_eval relay_st_s$s relay "prefix cap4" --relay age --quant 4
  ev relay_st_s${s}_none relay_st_s$s v6 "none"
  ev relay_ppo_s${s}_eval relay_ppo_s$s relay "prefix cap4" --relay age --quant 4
  ev relay_ppo_s${s}_none relay_ppo_s$s v6 "none"
done
for s in 5 6 7 8 9; do
  ev set_none_s$s set_none_s$s v6 "none"
  ev set_full_s$s set_full_s$s v6 "full prefix none"
  ev bb_set_full_s$s set_full_s$s v7 "prefix" --quant 4 --byte-capacity 3 --adapter-override freshonly
  ev distill_none_s$s distill_none_s$s v6 "none"
done
echo "evals 5-9 + relay pass done $(date)"
