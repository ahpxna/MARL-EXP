#!/usr/bin/env bash
# Auditor's test 3 (29/09): MARL_e3_label_horizon_probe.py on every actor with DEV labels, in 4 sequential lanes,
# each run under the CityFlow stall watchdog.  Output research/marl_budget/e3_label_horizon_20260929/<group>_<actor>.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1; PY=external_envs/runtime/bin/python
M=research/marl_budget; O=$M/e3_label_horizon_20260929; mkdir -p "$O"
one() {
  local n; n=$(echo "$1" | tr / _)
  [ -f "$O/$n/manifest.json" ] && { echo "done $n"; return 0; }
  "$PY" scripts/run_with_watchdog.py --log "$O/$n.log" --out "$O/$n" --stall 300 --retries 2 -- \
      "$PY" -u scripts/MARL_e3_label_horizon_probe.py --actor-dir "$M/$1" --cands 15 --out "$O/$n"
  echo "$n rc=$? $(date)"
}
lane() { for a in "$@"; do one "$a"; done; }
lane e3_scratch_seeds34_20260928/actor_s3 e3_run_20260928_003858/actor_s1 e3_scratch_rs_20260928/actor_s1 &
lane e3_run_seeds34_20260928/actor_s3 e3_run_20260928_003858/actor_s2 e3_scratch_rs_20260928/actor_s2 &
lane e3_run_20260928_003858/actor_s0 e3_run_seeds34_20260928/actor_s4 &
lane e3_scratch_rs_20260928/actor_s0 e3_scratch_rs_20260928/actor_s4 &
wait; echo "label horizon probe all lanes done $(date)"
