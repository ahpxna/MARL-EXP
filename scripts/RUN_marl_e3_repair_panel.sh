#!/usr/bin/env bash
# PROTOCOL_E3_REPAIR_PANEL_20261003.md (03/10/2026 18:3x EDT).  One JOB per call (the queue feeds jobs through xargs -P):
#   Z <s> | DET4 <CK1|Cage> <s> | C4 <CK1|Cage|MIX> <s> <K> | DET3 <CK1|Cage> <s> | RR4 <CK1|Cage> <s> <K> | RR3 <CK1|Cage> <s> <K>
# Main panel 4x4, traffic seeds 5301-5364 x 8/16; RR4 / RR3 = the corrected FB_Mq on EVERY cell of 4901 (4x4) / 4801 (3x3), with
# PLAIN reproduced against the stored RELAY rows.  SMOKE=1: traffic seeds 9001-9002, output under e3_repair_panel_20261003/smoke_pipe.
# Watchdog on every run; finished items (manifest present) are skipped; partial outputs go to legacy/, never deleted.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
M=research/marl_budget; E=$M/e3_repair_panel_20261003; [ "${SMOKE:-0}" = 1 ] && E=$E/smoke_pipe
A4=$M/e3_grid4x4_20260930/actors; A3=$M/e3_delivery_actors_20260929
W4="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
if [ "${SMOKE:-0}" = 1 ]; then S4="9001 9002"; S49="4901 4902"; S48="4801 4802"; else S4=$(seq 5301 5364); S49=$(seq 4901 4964); S48=$(seq 4801 4864); fi
DETS="FB_S+ FB_S- FB_M+ FB_M- FB_Mq+ FB_Mq-"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
wd() { local P=$1 tag=$2; shift 2; mkdir -p "$P"; [ -f "$P/$tag/manifest.json" ] && return 0; guard; fresh "$P/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$P/$tag.log" --out "$P/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$P/$tag" || echo "FAIL $tag"; }
name4() { case $1 in CK1) echo relayCK1_st;; Cage) echo relayCage_st;; MIX) echo relayMIX_st;; esac; }
name3() { case $1 in CK1) echo relayCK1_st;; Cage) echo relay6Cage_st;; esac; }
job=$1; shift
case $job in
  Z) s=$1; wd $E/4x4 Z_s$s $W4 scripts/MARL_e3_repair_panel_eval.py --z-only --z $A4/distill_none_s$s/ckpt_best.pt --traffic-seeds $S4 --headways 8 16 ;;
  DET4) r=$(name4 $1); s=$2; wd $E/4x4 det_${r}_s$s $W4 scripts/MARL_e3_repair_panel_eval.py --calibrate --relay $A4/${r}_s$s/ckpt_best.pt \
          --calib-old $M/e3_fallback_20261002/4x4/cal_${r}_s$s/calib.json $( [ "${SMOKE:-0}" = 1 ] && echo --calib-hi 332 ) ;;
  DET3) r=$(name3 $1); s=$2; wd $E/3x3_rerun det_${r}_s$s scripts/MARL_e3_repair_panel_eval.py --calibrate --relay $A3/${r}_s$s/ckpt_best.pt \
          --calib-old $M/e3_fallback_20261002/3x3/cal_${r}_s$s/calib.json ;;
  C4) r=$(name4 $1); s=$2; K=$3; D=$E/4x4/det_${r}_s$s/detectors.json
      case $1 in CK1) X="--arms PLAIN MASK $DETS EMU THR --ktrain 1 --floors $M/e3_age_emulation_20261003/4x4/cal_${r}_s$s/floors.json --detectors $D";;
                 Cage) X="--arms PLAIN MASK $DETS --detectors $D";; MIX) X="--arms PLAIN";; esac
      [ "$1" = MIX ] || [ -f "$D" ] || { echo "FAIL no detectors ${r}_s$s"; exit 1; }
      wd $E/4x4 RP_${r}_s${s}_K$K $W4 scripts/MARL_e3_repair_panel_eval.py --relay $A4/${r}_s$s/ckpt_best.pt --z $A4/distill_none_s$s/ckpt_best.pt \
        --tag ${r}_s$s --K $K $X --traffic-seeds $S4 --headways 8 16 ;;
  RR4) r=$(name4 $1); s=$2; K=$3; D=$E/4x4/det_${r}_s$s/detectors.json; [ -f "$D" ] || { echo "FAIL no detectors ${r}_s$s"; exit 1; }
      wd $E/rerun_4901 RR_${r}_s${s}_K$K $W4 scripts/MARL_e3_repair_panel_eval.py --relay $A4/${r}_s$s/ckpt_best.pt --z $A4/distill_none_s$s/ckpt_best.pt \
        --tag ${r}_s$s --K $K --arms PLAIN FB_Mq+ FB_Mq- --detectors $D --traffic-seeds $S49 --headways 8 16 \
        --parity "PLAIN=$M/e3_fallback_mahal_20261003/4x4/FBM_${r}_s${s}_K$K/rows.json:system=RELAY" ;;
  RR3) r=$(name3 $1); s=$2; K=$3; D=$E/3x3_rerun/det_${r}_s$s/detectors.json; [ -f "$D" ] || { echo "FAIL no detectors ${r}_s$s"; exit 1; }
      wd $E/rerun_4801 RR_${r}_s${s}_K$K scripts/MARL_e3_repair_panel_eval.py --relay $A3/${r}_s$s/ckpt_best.pt --z $A3/distill_none_s$s/ckpt_best.pt \
        --tag ${r}_s$s --K $K --arms PLAIN FB_Mq+ FB_Mq- --detectors $D --traffic-seeds $S48 --headways 8 16 \
        --parity "PLAIN=$M/e3_fallback_mahal_20261003/3x3/FBM_${r}_s${s}_K$K/rows.json:system=RELAY" ;;
  *) echo "unknown job $job"; exit 1 ;;
esac
echo "job $job $* done $(date)"
