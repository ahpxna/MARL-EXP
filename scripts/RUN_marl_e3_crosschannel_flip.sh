#!/usr/bin/env bash
# PROTOCOL_E3_CROSSCHANNEL_FLIP_20261003.md: 3x3 seeds 0-4, then 4x4 seeds 0-9 (grid relay wrapper), one process at a time, nice 15.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
P=research/marl_budget/e3_crosschannel_flip_20261003; mkdir -p $P
A=research/marl_budget/e3_delivery_actors_20260929
for s in 0 1 2 3 4; do
  [ -f $P/3x3_s$s/manifest.json ] && continue; R=""
  for a in relay6Cage_st relayCK1_st relayCK2_st relayMIX_st relayMIX2_st; do R="$R $a=$A/${a}_s$s/ckpt_best.pt"; done
  nice -n 15 $PY -u scripts/MARL_e3_crosschannel_flip_probe.py --z $A/distill_none_s$s/ckpt_best.pt --teacher $A/set_full_s$s/ckpt_best.pt \
    --receivers $R --out $P/3x3_s$s > $P/3x3_s$s.log 2>&1 || echo "FAIL 3x3_s$s"
done
G=research/marl_budget/e3_grid4x4_20260930/actors
for s in 0 1 2 3 4 5 6 7 8 9; do
  [ -f $P/4x4_s$s/manifest.json ] && continue
  nice -n 15 $PY -u scripts/MARL_grid_relay_wrapper.py --rows 4 --cols 4 --relay-slots nearest8 -- scripts/MARL_e3_crosschannel_flip_probe.py \
    --z $G/distill_none_s$s/ckpt_best.pt --teacher $G/set_full_s$s/ckpt_best.pt \
    --receivers relayCage_st=$G/relayCage_st_s$s/ckpt_best.pt relayCK1_st=$G/relayCK1_st_s$s/ckpt_best.pt --out $P/4x4_s$s > $P/4x4_s$s.log 2>&1 || echo "FAIL 4x4_s$s"
done
echo "crosschannel flip done $(date)"
