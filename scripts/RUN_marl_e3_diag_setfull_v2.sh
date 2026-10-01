#!/usr/bin/env bash
# D3 v2 (29/09 22:2x): RUN_marl_e3_diag_setfull.sh with every eval under scripts/run_with_watchdog.py (stall 300 s, --out,
# 3 retries).  v1's first eval deadlocked in CityFlow's pthread_cond_wait (CPU time frozen at 17 s), the known barrier hang.
# Output tags d3w_* (v1 tags stay with the hung v1 run, so the two scripts never share a directory).
# Question unchanged: is the set_full actor's capacity cliff caused by stale cached blocks it never saw in training?
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
A=set_full_s0=research/marl_budget/e3_delivery_actors_20260929/set_full_s0/ckpt_best.pt; E=research/marl_budget/e3_codesign_eval_20260929
JOBS=("d3w_setfull_freshonly|prefix cap6 cap4|iid|freshonly" "d3w_setfull_high|prefix full none|high|default" "d3w_setfull_high_freshonly|prefix|high|freshonly")
for j in "${JOBS[@]}"; do
  IFS='|' read -r tag dels cap ov <<< "$j"
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  [ -e "$E/$tag.log" ] && mv "$E/$tag.log" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S).log"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_v6.py --actors "$A" --deliveries $dels --capacity "$cap" --adapter-override "$ov" \
    --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
done
echo "D3 done $(date)"
