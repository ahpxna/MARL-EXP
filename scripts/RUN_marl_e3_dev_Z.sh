#!/usr/bin/env bash
# PROTOCOL_E3_HARM_PROSPECTIVE_ADDENDUM1_20261001.md comparator C4: distill_none_s0..9 on the DEVELOPMENT panel
# seed901-904 x 8/16 (the episodes of e3_protocol_demand_20261001).  Evaluations only, one lane.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_dev_Z_20261001; mkdir -p "$P"
for s in 0 1 2 3 4 5 6 7 8 9; do
  tag=Z_s$s
  [ -f "$P/$tag/manifest.json" ] && continue
  [ -e "$P/$tag" ] && mv "$P/$tag" "legacy/$(echo "$P/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_delivery_eval_v6.py \
    --actors "distill_none_s$s=$D/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds 901 902 903 904 --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
done
echo "dev-Z done $(date)"
