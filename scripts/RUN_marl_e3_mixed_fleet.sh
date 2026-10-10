#!/usr/bin/env bash
# PROTOCOL_E3_MIXED_FLEET_20261003.md (03/10/2026 20:2x EDT).  One JOB per call: REF <s> | MIX <s> <D|C>.  4x4, traffic 5901-5932 x 8/16.
# SMOKE=1: traffic 9001-9002 under e3_mixed_fleet_20261003/smoke_pipe.  Watchdog; finished items skipped; exit codes propagated.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
M=research/marl_budget; E=$M/e3_mixed_fleet_20261003; [ "${SMOKE:-0}" = 1 ] && E=$E/smoke_pipe; A=$M/e3_grid4x4_20260930/actors
W="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
if [ "${SMOKE:-0}" = 1 ]; then S="9001 9002"; else S=$(seq 5901 5932); fi
mkdir -p "$E"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
wd() { local tag=$1; shift; [ -f "$E/$tag/manifest.json" ] && return 0; guard; fresh "$E/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$E/$tag" || { echo "FAIL $tag"; return 1; }; }
C="--old $A/relayCK1_st_s$2/ckpt_best.pt --new $A/relayCage_st_s$2/ckpt_best.pt --z $A/distill_none_s$2/ckpt_best.pt"
case $1 in
  REF) wd REF_s$2 $W scripts/MARL_e3_mixed_fleet_eval.py $C --refs --traffic-seeds $S --headways 8 16 ;;
  MIX) wd MIX_s$2_$3 $W scripts/MARL_e3_mixed_fleet_eval.py $C --detectors $M/e3_repair_panel_20261003/4x4/det_relayCK1_st_s$2/detectors.json --layout $3 --traffic-seeds $S --headways 8 16 ;;
  *) echo "unknown job $1"; exit 1 ;;
esac
rc=$?; echo "job $* done rc=$rc $(date)"; exit $rc
