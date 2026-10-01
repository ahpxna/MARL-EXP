#!/usr/bin/env bash
# Novelty-direction test (29/09): MARL_e3_edit_ttl_probe.py with the strongest revert (L = 1) on the two actors with the
# largest random-edit full-episode harm per type (BC s4, BC s2) and two scratch actors (s3, rs s1), one process each,
# under the CityFlow stall watchdog.  Output research/marl_budget/e3_edit_ttl_20260929/<group>_<actor>.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
M=research/marl_budget; O=$M/e3_edit_ttl_20260929; H=$M/e3_label_horizon_20260929; mkdir -p "$O"
for a in e3_run_seeds34_20260928/actor_s4 e3_run_20260928_003858/actor_s2 e3_scratch_seeds34_20260928/actor_s3 e3_scratch_rs_20260928/actor_s1; do
  n=$(echo "$a" | tr / _)
  [ -f "$O/$n/manifest.json" ] && { echo "done $n"; continue; }
  ( "$PY" scripts/run_with_watchdog.py --log "$O/$n.log" --out "$O/$n" --stall 300 --retries 2 -- \
      "$PY" -u scripts/MARL_e3_edit_ttl_probe.py --actor-dir "$M/$a" --horizon-dir "$H/$n" --ttls 1 --cands 15 --out "$O/$n"; echo "$n rc=$? $(date)" ) &
done
wait; echo "edit ttl probe done $(date)"
