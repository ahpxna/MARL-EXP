#!/usr/bin/env bash
# Co-design evaluation (29/09 18:2x): a delivery-trained actor under its own delivery rule and under the prefix, on the
# 128 episodes of seeds 901-964 x 8/16 (the v2/v3 truncation runs' episodes), one output dir per actor so that
# MARL_e3_codesign_report.py compares it with the prefix system on the same episodes.
# Usage: bash scripts/RUN_marl_e3_codesign_eval.sh <tag> <ckpt> <delivery> [more deliveries...]
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
OUT=research/marl_budget/e3_codesign_eval_20260929; mkdir -p "$OUT"; tag="$1"; ck="$2"; shift 2
[ -f "$OUT/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
[ -e "$OUT/$tag" ] && mv "$OUT/$tag" "legacy/$(echo "$OUT/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
"$PY" -u scripts/MARL_e3_delivery_eval_v4.py --actors "$tag=$ck" --deliveries "$@" --traffic-seeds $(seq 901 964) --headways 8 16 --out "$OUT/$tag"
"$PY" scripts/MARL_e3_codesign_report.py --run "$OUT/$tag" --out "$OUT/${tag}_report"
