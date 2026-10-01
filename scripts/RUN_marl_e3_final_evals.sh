#!/usr/bin/env bash
# 128-episode evaluations of the finished co-design actors (29/09 21:4x), 3 lanes, then the consolidated papers report.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929
JOBS=("set_none_s0|none prefix|iid" "set_full_s0|full prefix none cap4 cap6|iid" "set_rxq_s0|rxq prefix none|iid"
      "set_rand_s0|random prefix none|iid" "rand_s0|random prefix none|iid" "fixcap_s0|prefix none|fixed" "nbrmask_s1|nbr prefix none|iid")
ev() {
  IFS='|' read -r tag dels cap <<< "$1"
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" -u scripts/MARL_e3_delivery_eval_v5.py --actors "$tag=$D/$tag/ckpt_best.pt" --deliveries $dels --capacity "$cap" \
    --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" > "$E/$tag.log" 2>&1 || echo "FAIL $tag"
}
lane() { local k="$1" n; for ((n = k; n < ${#JOBS[@]}; n += 3)); do ev "${JOBS[$n]}"; done; }
for k in 0 1 2; do lane $k & done
wait
"$PY" scripts/MARL_e3_papers_report.py
echo "final evals done $(date)"
