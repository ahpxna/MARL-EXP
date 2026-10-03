#!/usr/bin/env bash
# PROTOCOL_E3_MIXED_CHANNEL_20261001.md Addendum 1 (E4).  Usage: RUN_marl_e3_mixed_channel.sh <lane>
#   lane 0..3: train relayMIX_st_s<s> (v10, --capacity mix, resumable; watchdog WITHOUT --out) for the lane's seeds, then their
#              evaluations at K = 1, 2, 3, iid on panel 3801-3864;   lane cmp: Z and the comparators' evaluations.
# Skips anything with a manifest, so a rerun continues.  Report: scripts/MARL_e3_mixed_channel_report.py (after all lanes).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_mixed_channel_20261002; mkdir -p "$P"
SEEDS=$(seq 3801 3864)
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
evalR() {   # arm seed K
  local tag=R_$1_s$2_K$3; [ -f "$P/$tag/manifest.json" ] && return 0
  guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_ageclip_eval.py \
    --relay "$D/$1_s$2/ckpt_best.pt" --tag $1_s$2 --K $3 --A -1 --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
}
evalZ() {
  local tag=Z_s$1; [ -f "$P/$tag/manifest.json" ] && return 0
  guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_delivery_eval_v6.py \
    --actors "distill_none_s$1=$D/distill_none_s$1/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
}
case "$1" in
  0) LS="0 4 8" ;; 1) LS="1 5 9" ;; 2) LS="2 6" ;; 3) LS="3 7" ;;
  cmp)
    for s in 0 1 2 3 4 5 6 7 8 9; do
      evalZ $s
      for K in 1 0 2 3; do evalR relay6Cage_st $s $K; done
      [ $s -le 4 ] && for K in 1 0 2 3; do evalR relayCK1_st $s $K; done
      echo "cmp seed $s done $(date)"
    done
    echo "lane cmp done $(date)"; exit 0 ;;
  *) echo "unknown lane $1"; exit 2 ;;
esac
for s in $LS; do
  a=relayMIX_st_s$s
  if [ ! -f "$D/$a/manifest.json" ]; then
    guard; echo "train $a (v10 mix, resumable) $(date)"
    "$PY" scripts/run_with_watchdog.py --log "$D/$a.log" --stall 1200 --retries 20 -- "$PY" -u scripts/MARL_e3_actor_distill_v10.py \
      --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age --seed $s --iters 500 --quant 4 --order agefirst \
      --capacity mix --park-if-no-state --out "$D/$a" || { echo "FAIL $a"; continue; }
  fi
done
for s in $LS; do
  [ -f "$D/relayMIX_st_s$s/manifest.json" ] || { echo "SKIP evals relayMIX_st_s$s (no manifest)"; continue; }
  for K in 1 0 2 3; do evalR relayMIX_st $s $K; done
  echo "mix seed $s evals done $(date)"
done
echo "lane $1 done $(date)"
