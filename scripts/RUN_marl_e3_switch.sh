#!/usr/bin/env bash
# PROTOCOL_E3_SWITCH_20261002.md.  Usage: RUN_marl_e3_switch.sh <seed> [<seed> ...]   (3x3, panel 4401-4464)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_switch_20261002; mkdir -p "$P"; SEEDS=$(seq 4401 4464)
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
for s in "$@"; do
  tag=Z_s$s
  [ -f "$P/$tag/manifest.json" ] || { guard; fresh "$P/$tag"; "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_delivery_eval_v6.py \
    --actors "distill_none_s$s=$D/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"; }
  for arm in relayMIX_st relayCK1_st relay6Cage_st; do for sch in k1 iid k1_iid iid_k1 alt4; do
    tag=R_${arm}_s${s}_$sch; [ -f "$P/$tag/manifest.json" ] && continue; guard; fresh "$P/$tag"
    "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_switch_eval.py \
      --relay "$D/${arm}_s$s/ckpt_best.pt" --tag ${arm}_s$s --schedule $sch --A -1 --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
  done; done
  echo "switch seed $s done $(date)"
done
