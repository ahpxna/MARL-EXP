#!/usr/bin/env bash
# Queue of 02/10/2026 (user 15:1x; reviewed 16:5x): after the 4x4 train-match, test C (PROTOCOL_E3_MIX2_20261002), then
# test D (PROTOCOL_E3_G4_MIX_20261002).  Hard-link dedupe (finished runs only, nothing deleted) before C, before D and every
# 45 min while D runs; each test starts only if its panel is unused; C only if the v11 self-check passed.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
PY=external_envs/runtime/bin/python; M=research/marl_budget
dedupe() { echo "dedupe $(date) free $(df -g /System/Volumes/Data | awk 'NR==2{print $4}') GB"
  "$PY" -u scripts/UTIL_dedupe_hardlink.py --log $M/dedupe_hardlink_20261002.jsonl $M legacy | tail -1; }
echo "queue start $(date)"
for p in $(pgrep -f "RUN_marl_g4_train_match.sh"); do caffeinate -i -w "$p" 2>/dev/null; done
echo "4x4 train-match lanes done $(date)"
"$PY" scripts/MARL_e3_g4_train_match_report.py
grep -q '"verdict": "PASS"' $M/distill_v11_mix2_selfcheck_20261002/RESULT.json || { echo "v11 self-check not PASS: queue stopped"; exit 1; }
dedupe
"$PY" scripts/UTIL_panel_unused.py 4501 || { echo "panel 4501 used: C not started"; exit 1; }
for s in 0 1 2 3 4; do caffeinate -i bash scripts/RUN_marl_e3_mix2.sh "$s" > $M/e3_mix2_lane$s.log 2>&1 & done
wait
echo "C done $(date)"; grep -h "FAIL\|REFUSED" $M/e3_mix2_lane*.log
"$PY" scripts/MARL_e3_mixq_report.py --test C
dedupe
"$PY" scripts/UTIL_panel_unused.py 4601 || { echo "panel 4601 used: D not started"; exit 1; }
pids=()
for L in "0 5" "1 6" "2 7" "3 8" "4 9"; do
  caffeinate -i bash scripts/RUN_marl_g4_mix.sh $L > "$M/e3_g4_mix_lane${L// /_}.log" 2>&1 &
  pids+=($!)
done
( while kill -0 "${pids[0]}" 2>/dev/null || kill -0 "${pids[1]}" 2>/dev/null || kill -0 "${pids[2]}" 2>/dev/null || kill -0 "${pids[3]}" 2>/dev/null || kill -0 "${pids[4]}" 2>/dev/null; do
    sleep 2700; f=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "${f:-0}" -lt 25 ] && dedupe; done ) &
for p in "${pids[@]}"; do wait "$p"; done
echo "D done $(date)"; grep -h "FAIL\|REFUSED" $M/e3_g4_mix_lane*.log
"$PY" scripts/MARL_e3_mixq_report.py --test D
echo "queue end $(date)"
