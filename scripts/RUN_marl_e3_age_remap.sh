#!/usr/bin/env bash
# PROTOCOL_E3_AGE_REMAP_20261002.md.  Usage: RUN_marl_e3_age_remap.sh <seed> [<seed> ...]
# Per seed, panel 4001-4064 x 8/16: Z; plain relayCK1 / relay6Cage at K = 1, 2, 3, iid; remap relayCK1 (train K1) at K = 2, 3, iid
# and relay6Cage (train iid) at K = 1, 2, 3; identity checks (remap at the training channel, parity with the plain rows);
# clip A = 2 for relay6Cage at K = 1.  Idempotent.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_age_remap_20261002; mkdir -p "$P"
SEEDS=$(seq 4001 4064)
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
ev() {   # tag arm seed K extra-args...
  local tag=$1 arm=$2 s=$3 K=$4; shift 4
  [ -f "$P/$tag/manifest.json" ] && return 0
  guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_ageremap_eval.py \
    --relay "$D/${arm}_s$s/ckpt_best.pt" --tag ${arm}_s$s --K $K "$@" --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
}
for s in "$@"; do
  tag=Z_s$s
  [ -f "$P/$tag/manifest.json" ] || { guard; fresh "$P/$tag"; "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_delivery_eval_v6.py \
    --actors "distill_none_s$s=$D/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"; }
  for arm in relayCK1_st relay6Cage_st; do for K in 1 2 3 0; do ev P_${arm}_s${s}_K$K $arm $s $K --A -1; done; done
  for K in 2 3 0; do ev M_relayCK1_st_s${s}_K$K relayCK1_st $s $K --A -1 --remap 1; done
  for K in 1 2 3; do ev M_relay6Cage_st_s${s}_K$K relay6Cage_st $s $K --A -1 --remap 0; done
  ev I_relayCK1_st_s${s}_K1 relayCK1_st $s 1 --A -1 --remap 1 --parity "$P/P_relayCK1_st_s${s}_K1/rows.json"
  ev I_relay6Cage_st_s${s}_K0 relay6Cage_st $s 0 --A -1 --remap 0 --parity "$P/P_relay6Cage_st_s${s}_K0/rows.json"
  ev C_relay6Cage_st_s${s}_K1 relay6Cage_st $s 1 --A 2
  echo "remap seed $s done $(date)"
done
