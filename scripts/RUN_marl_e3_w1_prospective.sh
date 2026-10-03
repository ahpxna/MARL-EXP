#!/usr/bin/env bash
# PROTOCOL_E3_W1_PROSPECTIVE_20261002.md.  Usage: RUN_marl_e3_w1_prospective.sh <seed 0..4>
#   train relayCK2_st_s<s> (v9, --capacity const2, resumable; watchdog WITHOUT --out), then the seed's evaluations on panel
#   3901-3964: relayCK2 / relay6Cage / relayCK1 at K = 1, 2, 3, iid and Z.  Idempotent (skips anything with a manifest).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_w1_prospective_20261002; mkdir -p "$P"
SEEDS=$(seq 3901 3964); s=$1
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
evalR() {   # arm K
  local tag=R_$1_s${s}_K$2; [ -f "$P/$tag/manifest.json" ] && return 0
  guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_ageclip_eval.py \
    --relay "$D/$1_s$s/ckpt_best.pt" --tag $1_s$s --K $2 --A -1 --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
}
a=relayCK2_st_s$s
if [ ! -f "$D/$a/manifest.json" ]; then
  guard; echo "train $a (v9 const2, resumable) $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$D/$a.log" --stall 1200 --retries 20 -- "$PY" -u scripts/MARL_e3_actor_distill_v9.py \
    --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age --seed $s --iters 500 --quant 4 --order agefirst \
    --capacity const2 --park-if-no-state --out "$D/$a" || { echo "FAIL $a"; exit 1; }
fi
tag=Z_s$s
[ -f "$P/$tag/manifest.json" ] || { guard; fresh "$P/$tag"; "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_delivery_eval_v6.py \
  --actors "distill_none_s$s=$D/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"; }
for arm in relayCK2_st relay6Cage_st relayCK1_st; do for K in 1 2 3 0; do evalR $arm $K; done; done
echo "w1 seed $s done $(date)"
