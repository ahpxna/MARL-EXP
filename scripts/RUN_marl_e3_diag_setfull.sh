#!/usr/bin/env bash
# D3 (29/09 22:2x): is the set_full actor's capacity cliff (full -6.3 % vs its own none; prefix -0.5 %; cap4/cap6 +1.2..1.4 %)
# caused by STALE cached blocks it never saw in training (fixable at the receiver, 0 extra bytes), or by missing information?
# Eval-only, one lane.  Parity checked beforehand: v6 default reproduces v5 rows; freshonly under full is identical.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
A=set_full_s0=research/marl_budget/e3_delivery_actors_20260929/set_full_s0/ckpt_best.pt; E=research/marl_budget/e3_codesign_eval_20260929
JOBS=("diag_setfull_freshonly|prefix cap6 cap4|iid|freshonly" "diag_setfull_high|prefix full none|high|default" "diag_setfull_high_freshonly|prefix|high|freshonly")
for j in "${JOBS[@]}"; do
  IFS='|' read -r tag dels cap ov <<< "$j"
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" -u scripts/MARL_e3_delivery_eval_v6.py --actors "$A" --deliveries $dels --capacity "$cap" --adapter-override "$ov" \
    --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" > "$E/$tag.log" 2>&1 || echo "FAIL $tag"
done
echo "D3 done $(date)"
