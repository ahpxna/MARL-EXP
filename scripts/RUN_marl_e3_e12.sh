#!/usr/bin/env bash
# E12 (research/marl_budget/PROTOCOL_E3_E12_E14_G3_G6_20261004.md; 04/10/2026 wake 2): PANEL <s> = E7 panel 7501-7564 x headway 8/16,
# layouts D C, OLD on U2/EMU_OLD with a lockstep K1 reference (checks only).  Watchdog; skip finished; exit codes propagated.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
M=research/marl_budget; E=$M/e3_wave_20261003/e12; A=$M/e3_grid4x4_20260930/actors; mkdir -p "$E"
W="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
case $1 in
  PANEL) tag=PANEL_s$2; [ -f "$E/$tag/manifest.json" ] && exit 0; guard; fresh "$E/$tag"
    "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 900 --retries 3 -- "$PY" -u $W scripts/MARL_e3_emu_coverage_eval.py \
      --old $A/relayCK1_st_s$2/ckpt_best.pt --new $A/relayCage_st_s$2/ckpt_best.pt --layouts D C --traffic-seeds $(seq 7501 7564) --headways 8 16 --out "$E/$tag" || { echo "FAIL $tag"; exit 1; } ;;
  *) echo "unknown job $1"; exit 1 ;;
esac
echo "job $* done $(date)"
