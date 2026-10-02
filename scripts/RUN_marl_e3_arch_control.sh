#!/usr/bin/env bash
# PROTOCOL_E3_ARCH_CONTROL_20261001.md.  Usage: bash scripts/RUN_marl_e3_arch_control.sh <seed 0|1|2>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
s=$1; D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_arch_control_20261001; mkdir -p "$P"
SEEDS=$(seq 3601 3664)
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 10 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
for pair in attn:relayAttnCage_st sharedconcat:relaySCCage_st; do
  arch=${pair%%:*}; a=${pair##*:}_s$s
  if [ ! -f "$D/$a/manifest.json" ]; then
    guard; fresh "$D/$a"; echo "train $a $(date)"
    "$PY" scripts/run_with_watchdog.py --log "$D/$a.log" --out "$D/$a" --stall 1200 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill_v8.py \
      --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age --seed $s --iters 500 --quant 4 --order agefirst \
      --capacity iid --arch $arch --out "$D/$a" || echo "FAIL $a"
  fi
done
run() { local tag=$1; shift; [ -f "$P/$tag/manifest.json" ] && return 0; guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 600 --retries 3 -- "$PY" -u "$@" --out "$P/$tag" || echo "FAIL $tag"; }
run Z_s$s scripts/MARL_e3_delivery_eval_v6.py --actors "distill_none_s$s=$D/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16
for a in relayAttnCage_st relaySCCage_st relay6Cage_st; do
  [ -f "$D/${a}_s$s/manifest.json" ] || { echo "skip $a s$s"; continue; }
  for c in const1 const2 iid; do
    run R_${a}_s${s}_$c scripts/MARL_e3_delivery_eval_relay_v6.py --actors "${a}_s$s=$D/${a}_s$s/ckpt_best.pt" --deliveries prefix --capacity $c \
      --order agefirst --relay age --quant 4 --traffic-seeds $SEEDS --headways 8 16
  done
done
echo "arch-control seed $s done $(date)"
