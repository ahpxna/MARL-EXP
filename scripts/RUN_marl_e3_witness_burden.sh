#!/usr/bin/env bash
# PROTOCOL_E3_COMPAT_MAP_20261001.md Part C: witness burden on the nine order x capacity cells, seeds 0-9, development
# episodes 901-904 x 8/16, parity with the order-dose / viewstats-v2 flags.  One lane (single core).  Then the report.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_witness_burden_20261001; M=research/marl_budget; mkdir -p "$P"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 12 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
for s in 0 1 2 3 4 5 6 7 8 9; do
  for cell in prefix:iid:0:od prefix:cap4:0:od prefix:low:0:od agefirst:cap4:0:od agefirst:low:0:od agefirst:iid:0:vs agefirst:const1:1:vs agefirst:const2:2:vs agefirst:const3:3:vs; do
    IFS=: read o c K src <<< "$cell"; tag=${o}_${c}_s$s
    [ -f "$P/$tag/manifest.json" ] && continue
    if [ "$src" = od ]; then pd=$M/e3_order_dose_20261001/${o}_${c}_s$s; else pd=$M/e3_viewstats_v2_20261001/s${s}_K$K; fi
    cap=$c; [ "$K" != 0 ] && cap=iid
    guard; fresh "$P/$tag"
    "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_witness_burden_probe.py \
      --relay "$D/relay6Cage_st_s$s/ckpt_best.pt" --teacher "$D/set_full_s$s/ckpt_best.pt" --z "$D/distill_none_s$s/ckpt_best.pt" \
      --parity-dir "$pd" --K $K --order $o --capacity $cap --out "$P/$tag" || echo "FAIL $tag"
  done
  echo "seed $s done $(date)"
done
"$PY" scripts/MARL_e3_witness_burden_report.py
