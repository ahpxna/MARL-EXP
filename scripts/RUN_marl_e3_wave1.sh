#!/usr/bin/env bash
# Wave 1 of PROTOCOL_E3_WAVE_ALL_PENDING_20261003 (03/10/2026 23:3x EDT).  One JOB per call:
#   E6C <s> | E3 <s> | E11Z <s> | E11T <SCRATCH_NEW|SCRATCH_MIX|SCRATCH_MIX_T> <s> | E11E <ARM> <s> <B> <K>
# 4x4 (grid relay wrapper).  E6C: dev 901-904 x 8/16; E3: 7301-7332 x 8/16; E11: the adaptation pilot's blocks 5701-5748 x 8/16.
# SMOKE=1: traffic 9001-9002, budgets 8 16, under e3_wave_20261003/smoke_pipe.  Watchdog; finished items skipped; exit codes propagated.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
M=research/marl_budget; E=$M/e3_wave_20261003; [ "${SMOKE:-0}" = 1 ] && E=$E/smoke_pipe; A=$M/e3_grid4x4_20260930/actors
W="scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 --"
if [ "${SMOKE:-0}" = 1 ]; then DEV="9001 9002"; P3="9001 9002"; P11="9001 9002"; BUD="8 16"; BMAX=16; else DEV="901 902 903 904"; P3=$(seq 7301 7332); P11=$(seq 5701 5748); BUD="8 16 40 80"; BMAX=80; fi
mkdir -p "$E"
fresh() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"; return 0; }
guard() { local f; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 15 ] && { echo "REFUSED: $f GB free"; exit 1; }; return 0; }
wd() { local tag=$1; shift; [ -f "$E/$tag/manifest.json" ] && return 0; guard; fresh "$E/$tag"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 900 --retries 3 -- "$PY" -u "$@" --out "$E/$tag" || { echo "FAIL $tag"; return 1; }; }
targs() { case $1 in SCRATCH_NEW) echo "--method ft_new --from-scratch";; SCRATCH_MIX) echo "--method ft_mix --from-scratch";; SCRATCH_MIX_T) echo "--method ft_mix --from-scratch --beta0 1.0";; esac; }
R="$A/relayCK1_st_s"
case $1 in
  E6C) wd E6C_s$2 $W scripts/MARL_e3_emulator_rules_eval.py --relay ${R}$2/ckpt_best.pt --z $A/distill_none_s$2/ckpt_best.pt --arms K1/PLAIN U2/EXACT U2/EXACT_PACKET --traffic-seeds $DEV --headways 8 16 ;;
  E3) wd E3_s$2 $W scripts/MARL_e3_emulator_rules_eval.py --relay ${R}$2/ckpt_best.pt --z $A/distill_none_s$2/ckpt_best.pt --arms K1/PLAIN U1/PLAIN U1/EMU_OLDER U1/EMU_ABSENT U1/EMU_FRESH --traffic-seeds $P3 --headways 8 16 ;;
  E11Z) wd E11Z_s$2 $W scripts/MARL_e3_repair_panel_eval.py --z-only --z $A/distill_none_s$2/ckpt_best.pt --traffic-seeds $P11 --headways 8 16 ;;
  E11T) wd E11T_$2_s$3 $W scripts/MARL_e3_actor_adapt_v12.py --init-from ${R}$3/ckpt_best.pt $(targs $2) --seed $3 --budget $BMAX --save-at $BUD ;;
  E11E) c=$E/E11T_$2_s$3/ckpt_b$4.pt; [ -f "$c" ] || { echo "FAIL missing $c"; exit 1; }
        wd E11E_$2_s$3_B$4_K$5 $W scripts/MARL_e3_repair_panel_eval.py --relay $c --z $A/distill_none_s$3/ckpt_best.pt --tag $2_s$3_B$4 --arms PLAIN --K $5 --traffic-seeds $P11 --headways 8 16 ;;
  *) echo "unknown job $1"; exit 1 ;;
esac
rc=$?; echo "job $* done rc=$rc $(date)"; exit $rc
