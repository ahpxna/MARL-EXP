#!/usr/bin/env bash
# E9c (04/10/2026 00:4x EDT): DEV <s> (dev 901-904, layouts ALL D C, formats full wire4 wire5, 4 controls) | PANEL <s> (E7 panel 7501-7564, layouts D C, formats wire5 wire4).  Watchdog; skip finished; exit codes propagated.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
M=research/marl_budget; E=$M/e3_wave_20261003/e9c; A=$M/e3_grid4x4_20260930/actors; mkdir -p "$E"
W="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
wd() { local tag=$1; shift; [ -f "$E/$tag/manifest.json" ] && return 0; guard; fresh "$E/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$E/$tag" || { echo "FAIL $tag"; return 1; }; }
C="--old $A/relayCK1_st_s$2/ckpt_best.pt --new $A/relayCage_st_s$2/ckpt_best.pt --z $A/distill_none_s$2/ckpt_best.pt"
case $1 in
  DEV) wd DEV_s$2 $W scripts/MARL_e3_legacy_decoder_nodes_eval.py $C --layouts ALL D C --formats full wire4 wire5 --controls ages empty u2table stale --traffic-seeds 901 902 903 904 --headways 8 16 ;;
  PANEL) wd PANEL_s$2 $W scripts/MARL_e3_legacy_decoder_nodes_eval.py $C --layouts D C --formats wire5 wire4 --traffic-seeds $(seq 7501 7564) --headways 8 16 ;;
  *) echo "unknown job $1"; exit 1 ;;
esac
rc=$?; echo "job $* done rc=$rc $(date)"; exit $rc
