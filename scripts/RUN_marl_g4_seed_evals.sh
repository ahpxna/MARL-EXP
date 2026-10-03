#!/usr/bin/env bash
# PROTOCOL_E3_G4_RELAUNCH_20261002.md: the replication evaluations of ONE seed, commands copied verbatim from
# scripts/RUN_marl_g4_replication.sh (development parity eval Rdev low, V-D probe VD, target-panel Z, R iid, R low).
# Idempotent (skips COMPLETE manifests; partial outputs moved to legacy/).  Usage: bash scripts/RUN_marl_g4_seed_evals.sh <seed>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
A=research/marl_budget/e3_grid4x4_20260930/actors; E=research/marl_budget/e3_g4_replication_20261001; mkdir -p "$A" "$E"
W="scripts/MARL_grid_wrapper.py --rows 4 --cols 4 --"; WR="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 12 ] && { echo "REFUSED: ${f} GB free $(date)"; exit 1; }; return 0; }
fresh() { [ -e "$1" ] && mv "$1" "legacy/g4rep_$(basename "$1")_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
evr() {  # tag actor capacity deliveries seeds...
  local tag=$1 actor=$2 cap=$3 dels=$4; shift 4
  [ -f "$A/$actor/manifest.json" ] || { echo "skip $tag (no $actor)"; return 0; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  guard; fresh "$E/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 600 --retries 3 -- "$PY" -u $WR scripts/MARL_e3_delivery_eval_relay_satrot.py \
    --actors "$actor=$A/$actor/ckpt_best.pt" --deliveries $dels --capacity "$cap" --order agefirst --relay age --quant 4 \
    --traffic-seeds "$@" --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
s=$1
for x in set_full distill_none relayCage_st; do [ -f "$A/${x}_s$s/manifest.json" ] || { echo "no $x for s$s"; exit 1; }; done
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
for t in Rdev_s${s}_low VD_s$s Z_s$s R_s${s}_iid R_s${s}_low; do [ -f "$E/$t/manifest.json" ] || { echo "INCOMPLETE $t"; exit 1; }; done
echo "g4 seed $s evals done $(date)"
