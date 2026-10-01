#!/usr/bin/env bash
# Co-design check (29/09 18:2x): the FULL-delivery actor with its full stream truncated (MARL_e3_truncation_closed_loop_v3.py
# --base full), seeds 901-964 x 8/16 = 128 episodes, the same seeds as the v2/v3 prefix-actor runs.  Rules: full (225 B/step),
# blind caps 5..8, receiver proxy, proxy with staleness bounds 40/60/100 s, TMC 4.  One lane, one thread, under the watchdog.
# Usage: bash scripts/RUN_marl_e3_codesign_full.sh <tag> <ckpt>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
OUT=research/marl_budget/e3_codesign_full_20260929; mkdir -p "$OUT"; tag="$1"; ck="$2"
[ -f "$OUT/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
[ -e "$OUT/$tag" ] && mv "$OUT/$tag" "legacy/$(echo "$OUT/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
echo "launch $tag $(date)"
"$PY" scripts/run_with_watchdog.py --log "$OUT/$tag.log" --out "$OUT/$tag" --stall 600 --retries 2 -- "$PY" -u scripts/MARL_e3_truncation_closed_loop_v3.py \
  --base full --actor "$ck" --out "$OUT/$tag" --traffic-seeds $(seq 901 964) --headways 8 16 --capacity iid \
  --caps 5 6 7 8 --proxy --proxy-age 40 60 100 --tmc 4
echo "finished $tag rc=$? $(date)"
