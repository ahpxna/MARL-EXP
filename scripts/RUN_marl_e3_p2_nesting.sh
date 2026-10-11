#!/usr/bin/env bash
# PROTOCOL_E3_P2_NESTING_20261003.md (03/10/2026 18:4x EDT).  One JOB per call: Z <s> | R <CK1|Cage|MIX> <s>.
# 4x4 panel 5401-5464 x 8/16; SMOKE=1: traffic 9001-9002 under e3_p2_nesting_20261003/smoke_pipe.  Watchdog; finished items skipped.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
M=research/marl_budget; E=$M/e3_p2_nesting_20261003/4x4; [ "${SMOKE:-0}" = 1 ] && E=$M/e3_p2_nesting_20261003/smoke_pipe/4x4
A=$M/e3_grid4x4_20260930/actors; W="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
if [ "${SMOKE:-0}" = 1 ]; then S="9001 9002"; else S=$(seq 5401 5464); fi
mkdir -p "$E"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
wd() { local tag=$1; shift; [ -f "$E/$tag/manifest.json" ] && return 0; guard; fresh "$E/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$E/$tag" || { echo "FAIL $tag"; return 1; }; }   # exit code propagated (P2 Amendment 2)
case $1 in
  Z) wd Z_s$2 $W scripts/MARL_e3_p2_nesting_eval.py --z-only --z $A/distill_none_s$2/ckpt_best.pt --traffic-seeds $S --headways 8 16 ;;
  R) case $2 in CK1) r=relayCK1_st; X="--record-lock";; Cage) r=relayCage_st; X="--arms K1/PLAIN U1/PLAIN U2/PLAIN";; MIX) r=relayMIX_st; X="--arms K1/PLAIN U1/PLAIN U2/PLAIN";; esac
     wd NE_${r}_s$3 $W scripts/MARL_e3_p2_nesting_eval.py --relay $A/${r}_s$3/ckpt_best.pt --tag ${r}_s$3 $X --traffic-seeds $S --headways 8 16 ;;
  *) echo "unknown job $1"; exit 1 ;;
esac
rc=$?; echo "job $* done rc=$rc $(date)"; exit $rc
