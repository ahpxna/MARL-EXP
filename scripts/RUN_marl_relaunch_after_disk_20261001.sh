#!/usr/bin/env bash
# RELAUNCH after the 01/10 disk-full incident (ledger L-196).  Refuses to start with < 25 GB free.  Everything it calls is
# idempotent (skips work whose manifest.json exists; partial outputs are moved to legacy/, never deleted):
#   1. the overnight sweeper (3x3 lanes -> 4x4 phase 1 -> 4x4 phase 2 -> ten-seed panel -> overnight report), no waiting;
#   2. the V-D v2 probes (pair 0, pair 1, ten-seed a/b; empty + cache bases);
#   3. the frozen smoke gate of the 13 new MARL modules (incl. LeanMarlRevisionDepthV1), run name smokeMARLDD2_20261001.
# Usage: bash scripts/RUN_marl_relaunch_after_disk_20261001.sh
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
free_gb=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}')
if [ "${free_gb:-0}" -lt 25 ]; then echo "REFUSED: only ${free_gb} GB free (need >= 25)"; exit 1; fi
M=research/marl_budget; echo "relaunch $(date), ${free_gb} GB free"
nohup caffeinate -ims bash scripts/RUN_marl_overnight_sweeper_20260930.sh > $M/overnight_sweeper_relaunch_20261001.log 2>&1 &
echo "sweeper pid $!"
for a in "pair 0" "pair 1" "ten 0 2 4 6 8" "ten 1 3 5 7 9"; do
  tag=$(echo $a | tr ' ' '_')
  nohup caffeinate -i bash scripts/RUN_marl_e3_decision_depth_v2.sh $a > $M/decision_depth_v2_${tag}_relaunch.log 2>&1 &
  echo "V-D v2 $a pid $!"
done
cd work/p13_conjectures
RUN=smokeMARLDD2_20261001 J=2 GATE_ONLY="LeanMarlRelaySlotsV1 LeanMarlAgeFirstBreaksOneHopV1 LeanMarlNewsRelayV1 LeanMarlFloorAttainV1 LeanMarlPriceOfCoverageV1 LeanMarlStrongOneHopV1 LeanMarlRelayRevisionV1 LeanMarlDecisionDepthV1 LeanMarlPrefixEDFV1 LeanMarlObstructionMassV1 LeanMarlRelayDecisionV1 LeanMarlAdaptiveDepthV1 LeanMarlRevisionDepthV1" \
  nohup caffeinate -i bash verify_all.sh > ../gate_runs_smokeMARLDD2_20261001.log 2>&1 &
echo "gate pid $!"
