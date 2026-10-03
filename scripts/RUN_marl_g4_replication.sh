#!/usr/bin/env bash
# PROTOCOL_E3_G4_REPLICATION_20261001.md: 4x4 grid, seeds l and l+5 for lane l (0..4).  Per seed: teacher -> (zero-byte student
# || age-first relay student) -> development parity eval + N_s probe -> target panel 2901-2964.  Watchdog on every run;
# idempotent (skips anything with a COMPLETE manifest; partial outputs moved to legacy/, never deleted).
# Usage: bash scripts/RUN_marl_g4_replication.sh <lane 0..4>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
A=research/marl_budget/e3_grid4x4_20260930/actors; E=research/marl_budget/e3_g4_replication_20261001; mkdir -p "$A" "$E"
W="scripts/MARL_grid_wrapper.py --rows 4 --cols 4 --"; WR="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 12 ] && { echo "REFUSED: ${f} GB free $(date)"; exit 1; }; return 0; }
fresh() { [ -e "$1" ] && mv "$1" "legacy/g4rep_$(basename "$1")_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
train() {  # tag wrapper script args...
  local tag=$1 wr=$2; shift 2
  [ -f "$A/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  guard; fresh "$A/$tag"; echo "train $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$A/$tag.log" --out "$A/$tag" --stall 1200 --retries 3 -- "$PY" -u $wr "$@" --out "$A/$tag" || echo "FAIL $tag"
}
evr() {  # tag actor capacity deliveries seeds...
  local tag=$1 actor=$2 cap=$3 dels=$4; shift 4
  [ -f "$A/$actor/manifest.json" ] || { echo "skip $tag (no $actor)"; return 0; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  guard; fresh "$E/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 600 --retries 3 -- "$PY" -u $WR scripts/MARL_e3_delivery_eval_relay_satrot.py \
    --actors "$actor=$A/$actor/ckpt_best.pt" --deliveries $dels --capacity "$cap" --order agefirst --relay age --quant 4 \
    --traffic-seeds "$@" --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
TR="--iters 2000 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 --eval-every 20 --threads 2 --set-actor"
for s in $1 $(( $1 + 5 )); do
  train set_full_s$s "$W" scripts/MARL_e3_actor_train_delivery_v6.py --seed $s $TR --delivery full
  [ -f "$A/set_full_s$s/manifest.json" ] || { echo "no teacher for s$s"; continue; }
  train distill_none_s$s "$W" scripts/MARL_e3_actor_distill.py --teacher "$A/set_full_s$s/ckpt_best.pt" --student-delivery none --seed $s --iters 500 --threads 2 &
  train relayCage_st_s$s "$WR" scripts/MARL_e3_actor_distill_v6.py --teacher "$A/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age \
    --seed $s --iters 500 --quant 4 --order agefirst &
  wait
  evr Rdev_s${s}_low relayCage_st_s$s low prefix $(seq 901 932)
  if [ -f "$E/Rdev_s${s}_low/manifest.json" ] && [ ! -f "$E/VD_s$s/manifest.json" ]; then
    guard; fresh "$E/VD_s$s"
    "$PY" scripts/run_with_watchdog.py --log "$E/VD_s$s.log" --out "$E/VD_s$s" --stall 900 --retries 3 -- "$PY" -u $WR scripts/MARL_e3_decision_depth_probe.py \
      --relay "$A/relayCage_st_s$s/ckpt_best.pt" --teacher "$A/set_full_s$s/ckpt_best.pt" --order agefirst --rule prefix --capacity low \
      --traffic-seeds $(seq 901 932) --headways 8 16 --parity "$E/Rdev_s${s}_low/rows.json" --out "$E/VD_s$s" || echo "FAIL VD_s$s"
  fi
  if [ -f "$A/distill_none_s$s/manifest.json" ] && [ ! -f "$E/Z_s$s/manifest.json" ]; then
    guard; fresh "$E/Z_s$s"
    "$PY" scripts/run_with_watchdog.py --log "$E/Z_s$s.log" --out "$E/Z_s$s" --stall 600 --retries 3 -- "$PY" -u $W scripts/MARL_e3_delivery_eval_v6.py \
      --actors "distill_none_s$s=$A/distill_none_s$s/ckpt_best.pt" --deliveries none --capacity iid --traffic-seeds $(seq 2901 2964) --headways 8 16 \
      --out "$E/Z_s$s" || echo "FAIL Z_s$s"
  fi
  evr R_s${s}_iid relayCage_st_s$s iid "prefix cap4" $(seq 2901 2964)
  evr R_s${s}_low relayCage_st_s$s low prefix $(seq 2901 2964)
done
echo "g4 replication lane $1 done $(date)"
