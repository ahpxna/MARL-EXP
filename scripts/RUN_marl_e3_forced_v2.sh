#!/usr/bin/env bash
# Route 2 data (MARL_DEEP_RESEARCH_20260929.md): forced single-agent action changes with the actor inputs saved
# (MARL_e3_forced_action_probe_v2.py) on the TRAIN (5 shards), SELECT and DEV states of one actor, under the watchdog.
# Output research/marl_budget/e3_forced_v2_20260929/<group>_<actor>/<split>_<k>.  Usage: bash RUN_marl_e3_forced_v2.sh <actor rel dir>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
M=research/marl_budget; A="${1:?actor rel dir}"; O=$M/e3_forced_v2_20260929/$(echo "$A" | tr / _); mkdir -p "$O"
one() {  # split-glob tag shard nshards
  local out="$O/$2_$3"; [ -f "$out/manifest.json" ] && { echo "done $out"; return 0; }
  "$PY" scripts/run_with_watchdog.py --log "$out.log" --out "$out" --stall 300 --retries 2 -- \
      "$PY" -u scripts/MARL_e3_forced_action_probe_v2.py --actor-dir "$M/$A" --labels "$1" --shard $3 --nshards $4 --out "$out"
  echo "$out rc=$? $(date)"
}
for k in 0 1 2 3 4; do one 'labels_train_*' train $k 5 & done
one labels_select select 0 1 &
one labels_dev dev 0 1 &
wait; echo "forced v2 $A done $(date)"
