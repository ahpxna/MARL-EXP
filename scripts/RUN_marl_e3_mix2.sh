#!/usr/bin/env bash
# PROTOCOL_E3_MIX2_20261002.md (test C, 3x3).  Usage: RUN_marl_e3_mix2.sh <seed> [<seed> ...]   (panel 4501-4564)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_mix2_20261002; mkdir -p "$P"; SEEDS=$(seq 4501 4564)
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
for s in "$@"; do
  a=relayMIX2_st_s$s
  if [ ! -f "$D/$a/manifest.json" ]; then
    guard; echo "train $a (v11 mix iid,const1) $(date)"
    "$PY" scripts/run_with_watchdog.py --log "$D/$a.log" --stall 1200 --retries 20 -- "$PY" -u scripts/MARL_e3_actor_distill_v11.py \
      --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age --seed $s --iters 500 --quant 4 --order agefirst \
      --capacity mix --mix-regimes iid,const1 --park-if-no-state --out "$D/$a" || { echo "FAIL $a"; continue; }
  fi
  tag=Z_s$s
  [ -f "$P/$tag/manifest.json" ] || { guard; fresh "$P/$tag"; "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_delivery_eval_v6.py \
    --actors "distill_none_s$s=$D/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"; }
  for arm in relayMIX2_st relayMIX_st relay6Cage_st relayCK1_st; do for K in 1 2 3 0; do
    tag=R_${arm}_s${s}_K$K; [ -f "$P/$tag/manifest.json" ] && continue; guard; fresh "$P/$tag"
    "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_ageclip_eval.py \
      --relay "$D/${arm}_s$s/ckpt_best.pt" --tag ${arm}_s$s --K $K --A -1 --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
  done; done
  echo "mix2 seed $s done $(date)"
done
