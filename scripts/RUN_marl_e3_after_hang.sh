#!/usr/bin/env bash
# Relaunch everything after the CityFlow hang of 28/09 (run AFTER: pkill -9 -f "scripts/MARL_e3_").
# Three lanes, each under the watchdog: (1) BC chains resume, then frontier/shift for their actors;
# (2) scratch chains resume, then frontier/shift; (3) learned SchedNet v2 (1-byte weights) for the two gated actors.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"; M=research/marl_budget
# IGNORE_HUNG=1: proceed while the deadlocked processes still exist (verified: 0% CPU for hours, stack in CityFlow's
# pthread_cond_wait).  They never write again; the resume runners only touch partial dirs (parked in legacy/).
if [ "${IGNORE_HUNG:-0}" != 1 ] && pgrep -f "python.*scripts/MARL_e3_" > /dev/null; then echo "hung MARL_e3 processes still alive: kill them first (or IGNORE_HUNG=1)"; exit 2; fi
pgrep -f "python.*scripts/MARL_e3_" | tr "\n" " " > $M/e3_hung_pids_at_relaunch.txt || true
export SKIP_HANG_GUARD=1      # checked once here; the lanes start MARL_e3 processes of their own
( bash scripts/RUN_marl_e3_resume.sh $M/e3_run_20260928_003858 bc "0 1 2"; bash scripts/RUN_marl_e3_resume.sh $M/e3_run_seeds34_20260928 bc "3 4";
  bash scripts/RUN_marl_e3_frontier.sh $M/e3_run_20260928_003858/actor_s{0,1,2} $M/e3_run_seeds34_20260928/actor_s{3,4} ) > $M/e3_lane_bc.log 2>&1 &
( sleep 5; bash scripts/RUN_marl_e3_resume.sh $M/e3_scratch_seeds34_20260928 scratch "3 4"; bash scripts/RUN_marl_e3_resume.sh $M/e3_scratch_20260928_0043 scratch "0 1 2";
  bash scripts/RUN_marl_e3_frontier.sh $M/e3_scratch_seeds34_20260928/actor_s{3,4} $M/e3_scratch_20260928_0043/actor_s{0,1,2} ) > $M/e3_lane_scratch.log 2>&1 &
( sleep 10; bash scripts/RUN_marl_e3_schednet_resume.sh $M/e3_schednet_v2_20260928 $M/e3_scratch_seeds34_20260928/actor_s3/ckpt_best.pt $M/e3_run_seeds34_20260928/actor_s3/ckpt_best.pt ) > $M/e3_lane_schednet.log 2>&1 &
echo "launched 3 lanes $(date); logs: $M/e3_lane_{bc,scratch,schednet}.log"; wait; echo "ALL LANES DONE $(date)"
