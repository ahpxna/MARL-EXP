#!/usr/bin/env bash
# PROTOCOL_E3_MISMATCH_LAW_20261002.md: panel 3701-3764 x 8/16 (used once), seeds 0-3, one lane, then the report.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_mismatch_law_20261002; mkdir -p "$P"
SEEDS=$(seq 3701 3764)
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 12 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
run() { local tag=$1; shift; [ -f "$P/$tag/manifest.json" ] && return 0; guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u "$@" --out "$P/$tag" || echo "FAIL $tag"; }
for s in 0 1 2 3; do
  run Z_s$s scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s$s=$D/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16
  for arm in relayCK1_st relay6Cage_st; do
    for K in 1 2 3 0; do
      run R_${arm}_s${s}_K$K scripts/MARL_e3_ageclip_eval.py --relay "$D/${arm}_s$s/ckpt_best.pt" --tag ${arm}_s$s --K $K --A -1 --traffic-seeds $SEEDS --headways 8 16
    done
  done
  echo "seed $s done $(date)"
done
"$PY" scripts/MARL_e3_mismatch_law_report.py
