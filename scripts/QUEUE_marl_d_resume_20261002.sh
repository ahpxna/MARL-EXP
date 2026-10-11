#!/usr/bin/env bash
# Resume of test D (PROTOCOL_E3_G4_MIX_20261002.md) after the 02/10/2026 22:08 EDT session exit killed the lanes of
# scripts/QUEUE_marl_cd_20261002.sh 16 min into training (the v11 trainer is resumable from state_last.pt; the panel 4601 check
# passed at 21:52 and again at 22:1x).  Lines 23-33 of that queue, unchanged otherwise.  Launched detached (nohup) in the
# user's terminal so a session exit cannot kill it again.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
PY=external_envs/runtime/bin/python; M=research/marl_budget
dedupe() { echo "dedupe $(date) free $(df -g /System/Volumes/Data | awk 'NR==2{print $4}') GB"
  "$PY" -u scripts/UTIL_dedupe_hardlink.py --log $M/dedupe_hardlink_20261002.jsonl $M legacy | tail -1; }
echo "D resume start $(date)"
pids=()
for L in "0 5" "1 6" "2 7" "3 8" "4 9"; do
  caffeinate -i bash scripts/RUN_marl_g4_mix.sh $L >> "$M/e3_g4_mix_lane${L// /_}.log" 2>&1 &
  pids+=($!)
done
( while kill -0 "${pids[0]}" 2>/dev/null || kill -0 "${pids[1]}" 2>/dev/null || kill -0 "${pids[2]}" 2>/dev/null || kill -0 "${pids[3]}" 2>/dev/null || kill -0 "${pids[4]}" 2>/dev/null; do
    sleep 2700; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 25 ] && dedupe; done ) &
for p in "${pids[@]}"; do wait "$p"; done
echo "D done $(date)"; grep -h "FAIL\|REFUSED" $M/e3_g4_mix_lane*.log
"$PY" scripts/MARL_e3_mixq_report.py --test D
echo "queue end $(date)"
