#!/usr/bin/env bash
# D4 (29/09 22:4x), eval-only: the components the current E3 pipeline USES, tested against lessons of the old papers' experiments.
#  (a) stream order / receiver decode rule under the fresh-only receiver (FO):
#      prefix (cached-waiting plug-in ranking; Paper A: a plug-in surrogate starves, 39 % censored runs),
#      nbr (physical neighbours first; QUERY: distance-1 signal is always present, farther needs horizon >= distance),
#      rxold (oldest first, bounded age; ADAPTIVE), random (uniform order; Paper A's uniform arm, Paper C's band),
#      rxq (receiver's own-cache waiting; MASTER/B receiver-side query).
#  (b) checkpoint selection (SELECT min over 100 noisy evaluations; Paper A7's certified-stopping lesson, L-111):
#      the LAST checkpoints of set_full_s0 (FO and full) and set_none_s0, instead of ckpt_best.
# Watchdog on every eval (stall 300 s, --out, 3 retries); development panel 901-964 x 8/16.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929
JOBS=("d4_fo_orders|set_full_s0=$D/set_full_s0/ckpt_best.pt|nbr rxold random rxq|freshonly"
      "d4_last_fo|set_full_s0_last=$D/set_full_s0/ckpt_last.pt|prefix cap4|freshonly"
      "d4_last_def|set_full_s0_last=$D/set_full_s0/ckpt_last.pt set_none_s0_last=$D/set_none_s0/ckpt_last.pt|full none|default")
for j in "${JOBS[@]}"; do
  IFS='|' read -r tag actors dels ov <<< "$j"
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_v6.py --actors $actors --deliveries $dels --capacity iid --adapter-override "$ov" \
    --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
done
echo "D4 done $(date)"
