#!/usr/bin/env bash
# PROTOCOL_E3_TRAIN_MATCH_K1_20261001.md Deviation 1: relayCK1_st_s4 with the exact-resume trainer v9 (watchdog WITHOUT --out),
# then seed 4's evaluations (as RUN_marl_e3_train_match.sh) and the report.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; P=research/marl_budget/e3_train_match_20261001; s=4; a=relayCK1_st_s$s
SEEDS=$(seq 3201 3264)
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
if [ ! -f "$D/$a/manifest.json" ]; then
  guard; [ -e "$D/$a" ] && [ ! -f "$D/$a/state_last.pt" ] && fresh "$D/$a"; echo "train $a (v9, resumable) $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$D/$a.log" --stall 1200 --retries 20 -- "$PY" -u scripts/MARL_e3_actor_distill_v9.py \
    --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age --seed $s --iters 500 --quant 4 --order agefirst \
    --capacity const1 --park-if-no-state --out "$D/$a" || { echo "FAIL $a"; exit 1; }
fi
tag=NF_s${s}_K1
[ -f "$P/$tag/manifest.json" ] || { guard; fresh "$P/$tag"; "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_negflip_probe.py \
  --relay "$D/$a/ckpt_best.pt" --teacher "$D/set_full_s$s/ckpt_best.pt" --z "$D/distill_none_s$s/ckpt_best.pt" \
  --zrows "research/marl_budget/e3_dev_Z_20261001/Z_s$s/rows.json" --K 1 --out "$P/$tag" || echo "FAIL $tag"; }
tag=Z_s$s
[ -f "$P/$tag/manifest.json" ] || { guard; fresh "$P/$tag"; "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_delivery_eval_v6.py \
  --actors "distill_none_s$s=$D/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"; }
for arm in relayCK1_st relay6Cage_st; do
  for K in 1 0; do
    tag=R_${arm}_s${s}_K$K; [ -f "$P/$tag/manifest.json" ] && continue
    guard; fresh "$P/$tag"
    "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 300 --retries 3 -- "$PY" -u scripts/MARL_e3_ageclip_eval.py \
      --relay "$D/${arm}_s$s/ckpt_best.pt" --tag ${arm}_s$s --K $K --A -1 --traffic-seeds $SEEDS --headways 8 16 --out "$P/$tag" || echo "FAIL $tag"
  done
done
echo "seed-4 lane done $(date)"
"$PY" scripts/MARL_e3_train_match_report.py
